import Waring.SeedCompletionAlternate9Steps03

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionAlternate9Seeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges SeedCompletionDivisorPowerScales
open PolicyCompletionSharpResidualSource

private def half_20_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1094804139/10000000000 : ℝ)

private theorem half_20_03_total1 : total half_20_03_φ1=(1094804139/10000000000 : ℝ) := by
  norm_num [half_20_03_φ1,total,emptyPhi,Fin.snoc]

private theorem half_20_03_bounds1 : ∀ l,0≤half_20_03_φ1 l ∧ half_20_03_φ1 l≤1 ∧
    0≤shiftExponents 9 half_20_03_φ1 l :=
  alternate_bounds_snoc emptyPhi (1094804139/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_20_03_φ2 : Fin 2 → ℝ := Fin.snoc half_20_03_φ1 (536822599/5000000000 : ℝ)

private theorem half_20_03_total2 : total half_20_03_φ2=(2168449337/10000000000 : ℝ) := by
  change total (Fin.snoc half_20_03_φ1 (536822599/5000000000 : ℝ))=(2168449337/10000000000 : ℝ)
  rw [alternate_total_snoc,half_20_03_total1]
  norm_num

private theorem half_20_03_bounds2 : ∀ l,0≤half_20_03_φ2 l ∧ half_20_03_φ2 l≤1 ∧
    0≤shiftExponents 9 half_20_03_φ2 l :=
  alternate_bounds_snoc half_20_03_φ1 (536822599/5000000000 : ℝ) half_20_03_bounds1 (by norm_num)

private def half_20_03_φ3 : Fin 3 → ℝ := Fin.snoc half_20_03_φ2 (122367979/1250000000 : ℝ)

private theorem half_20_03_total3 : total half_20_03_φ3=(3147393169/10000000000 : ℝ) := by
  change total (Fin.snoc half_20_03_φ2 (122367979/1250000000 : ℝ))=(3147393169/10000000000 : ℝ)
  rw [alternate_total_snoc,half_20_03_total2]
  norm_num

private theorem half_20_03_bounds3 : ∀ l,0≤half_20_03_φ3 l ∧ half_20_03_φ3 l≤1 ∧
    0≤shiftExponents 9 half_20_03_φ3 l :=
  alternate_bounds_snoc half_20_03_φ2 (122367979/1250000000 : ℝ) half_20_03_bounds2 (by norm_num)

private def half_20_03_φ4 : Fin 4 → ℝ := Fin.snoc half_20_03_φ3 (856575853/10000000000 : ℝ)

private theorem half_20_03_total4 : total half_20_03_φ4=(2001984511/5000000000 : ℝ) := by
  change total (Fin.snoc half_20_03_φ3 (856575853/10000000000 : ℝ))=(2001984511/5000000000 : ℝ)
  rw [alternate_total_snoc,half_20_03_total3]
  norm_num

private theorem half_20_03_bounds4 : ∀ l,0≤half_20_03_φ4 l ∧ half_20_03_φ4 l≤1 ∧
    0≤shiftExponents 9 half_20_03_φ4 l :=
  alternate_bounds_snoc half_20_03_φ3 (856575853/10000000000 : ℝ) half_20_03_bounds3 (by norm_num)

private def half_20_03_φ5 : Fin 5 → ℝ := Fin.snoc half_20_03_φ4 (5855499/78125000 : ℝ)

private theorem half_20_03_total5 : total half_20_03_φ5=(2376736447/5000000000 : ℝ) := by
  change total (Fin.snoc half_20_03_φ4 (5855499/78125000 : ℝ))=(2376736447/5000000000 : ℝ)
  rw [alternate_total_snoc,half_20_03_total4]
  norm_num

private theorem half_20_03_bounds5 : ∀ l,0≤half_20_03_φ5 l ∧ half_20_03_φ5 l≤1 ∧
    0≤shiftExponents 9 half_20_03_φ5 l :=
  alternate_bounds_snoc half_20_03_φ4 (5855499/78125000 : ℝ) half_20_03_bounds4 (by norm_num)

private def half_20_03_φ6 : Fin 6 → ℝ := Fin.snoc half_20_03_φ5 (40988493/625000000 : ℝ)

private theorem half_20_03_total6 : total half_20_03_φ6=(2704644391/5000000000 : ℝ) := by
  change total (Fin.snoc half_20_03_φ5 (40988493/625000000 : ℝ))=(2704644391/5000000000 : ℝ)
  rw [alternate_total_snoc,half_20_03_total5]
  norm_num

private theorem half_20_03_bounds6 : ∀ l,0≤half_20_03_φ6 l ∧ half_20_03_φ6 l≤1 ∧
    0≤shiftExponents 9 half_20_03_φ6 l :=
  alternate_bounds_snoc half_20_03_φ5 (40988493/625000000 : ℝ) half_20_03_bounds5 (by norm_num)

private theorem half_20_03_prefix : PrefixCondition 9 half_20_03_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_20_03_φ1, half_20_03_φ2, half_20_03_φ3, half_20_03_φ4, half_20_03_φ5, half_20_03_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_20_03_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_20_03_φ6) (4386066827/625000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_20_03_φ6
    (fun i => (half_20_03_bounds6 i).1) (fun i => (half_20_03_bounds6 i).2.1)
    (fun i => (half_20_03_bounds6 i).2.2) half_20_03_prefix
  convert h using 1 <;> norm_num [half_20_03_total1, half_20_03_total2, half_20_03_total3, half_20_03_total4, half_20_03_total5, half_20_03_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_20_03_hx6 : SourcePowerBound
    (powerBoxCross 9 14 64 half_20_03_φ6) (116047140417/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 14) (r := 2) (v := 18) (w := 19) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_20_03_φ6 (by norm_num [half_20_03_total1, half_20_03_total2, half_20_03_total3, half_20_03_total4, half_20_03_total5, half_20_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_20_03_total1, half_20_03_total2, half_20_03_total3, half_20_03_total4, half_20_03_total5, half_20_03_total6, parameterExponent, curveLoss, dyadicExponent]) half_20_03_hF2
    (half_18_03) (half_19_03)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_20_03_total1, half_20_03_total2, half_20_03_total3, half_20_03_total4, half_20_03_total5, half_20_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_03_hx5 : SourcePowerBound
    (powerBoxCross 9 15 32 half_20_03_φ5) (3361725613/250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 15) (u := 13) (t := 16)
    (D := 32) (ψ := (40988493/625000000 : ℝ)) half_20_03_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_03_bounds5 l).1) (fun l => (half_20_03_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_03_total1, half_20_03_total2, half_20_03_total3, half_20_03_total4, half_20_03_total5, half_20_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_03) (half_16_03)
    (by simpa only [half_20_03_φ6, show (2:ℝ)*32=64 by norm_num] using half_20_03_hx6)
  exact h.weaken (by norm_num [half_20_03_total1, half_20_03_total2, half_20_03_total3, half_20_03_total4, half_20_03_total5, half_20_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_03_hx4 : SourcePowerBound
    (powerBoxCross 9 16 16 half_20_03_φ4) (79101935581/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 16) (u := 14) (t := 17)
    (D := 16) (ψ := (5855499/78125000 : ℝ)) half_20_03_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_03_bounds4 l).1) (fun l => (half_20_03_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_03_total1, half_20_03_total2, half_20_03_total3, half_20_03_total4, half_20_03_total5, half_20_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_03) (half_17_03)
    (by simpa only [half_20_03_φ5, show (2:ℝ)*16=32 by norm_num] using half_20_03_hx5)
  exact h.weaken (by norm_num [half_20_03_total1, half_20_03_total2, half_20_03_total3, half_20_03_total4, half_20_03_total5, half_20_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_03_hx3 : SourcePowerBound
    (powerBoxCross 9 17 8 half_20_03_φ3) (47094266491/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 17) (u := 15) (t := 18)
    (D := 8) (ψ := (856575853/10000000000 : ℝ)) half_20_03_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_03_bounds3 l).1) (fun l => (half_20_03_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_03_total1, half_20_03_total2, half_20_03_total3, half_20_03_total4, half_20_03_total5, half_20_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_03) (half_18_03)
    (by simpa only [half_20_03_φ4, show (2:ℝ)*8=16 by norm_num] using half_20_03_hx4)
  exact h.weaken (by norm_num [half_20_03_total1, half_20_03_total2, half_20_03_total3, half_20_03_total4, half_20_03_total5, half_20_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_03_hx2 : SourcePowerBound
    (powerBoxCross 9 18 4 half_20_03_φ2) (226230131691/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 18) (u := 16) (t := 19)
    (D := 4) (ψ := (122367979/1250000000 : ℝ)) half_20_03_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_03_bounds2 l).1) (fun l => (half_20_03_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_03_total1, half_20_03_total2, half_20_03_total3, half_20_03_total4, half_20_03_total5, half_20_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_03) (half_19_03)
    (by simpa only [half_20_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_20_03_hx3)
  exact h.weaken (by norm_num [half_20_03_total1, half_20_03_total2, half_20_03_total3, half_20_03_total4, half_20_03_total5, half_20_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_03_hx1 : SourcePowerBound
    (powerBoxCross 9 19 2 half_20_03_φ1) (67907952193/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 19) (u := 17) (t := 20)
    (D := 2) (ψ := (536822599/5000000000 : ℝ)) half_20_03_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_03_bounds1 l).1) (fun l => (half_20_03_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_03_total1, half_20_03_total2, half_20_03_total3, half_20_03_total4, half_20_03_total5, half_20_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_03) (chord_68)
    (by simpa only [half_20_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_20_03_hx2)
  exact h.weaken (by norm_num [half_20_03_total1, half_20_03_total2, half_20_03_total3, half_20_03_total4, half_20_03_total5, half_20_03_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_20_03 : AdmissibleExponent 9 40 (62427912383/2000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 18) (ψ := (1094804139/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_19_03)
    (by simpa only [half_20_03_φ1] using half_20_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_20_03_total1, half_20_03_total2, half_20_03_total3, half_20_03_total4, half_20_03_total5, half_20_03_total6, parameterExponent, curveLoss, dyadicExponent])

theorem chord_69 : AdmissibleExponent 9 42 (664446484633/20000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 42) (t := (1/2 : ℝ))
    (half_20_03) (half_22_02)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_21_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1106977671/10000000000 : ℝ)

private theorem half_21_03_total1 : total half_21_03_φ1=(1106977671/10000000000 : ℝ) := by
  norm_num [half_21_03_φ1,total,emptyPhi,Fin.snoc]

private theorem half_21_03_bounds1 : ∀ l,0≤half_21_03_φ1 l ∧ half_21_03_φ1 l≤1 ∧
    0≤shiftExponents 9 half_21_03_φ1 l :=
  alternate_bounds_snoc emptyPhi (1106977671/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_21_03_φ2 : Fin 2 → ℝ := Fin.snoc half_21_03_φ1 (43328001/400000000 : ℝ)

private theorem half_21_03_total2 : total half_21_03_φ2=(68443053/312500000 : ℝ) := by
  change total (Fin.snoc half_21_03_φ1 (43328001/400000000 : ℝ))=(68443053/312500000 : ℝ)
  rw [alternate_total_snoc,half_21_03_total1]
  norm_num

private theorem half_21_03_bounds2 : ∀ l,0≤half_21_03_φ2 l ∧ half_21_03_φ2 l≤1 ∧
    0≤shiftExponents 9 half_21_03_φ2 l :=
  alternate_bounds_snoc half_21_03_φ1 (43328001/400000000 : ℝ) half_21_03_bounds1 (by norm_num)

private def half_21_03_φ3 : Fin 3 → ℝ := Fin.snoc half_21_03_φ2 (976227787/10000000000 : ℝ)

private theorem half_21_03_total3 : total half_21_03_φ3=(3166405483/10000000000 : ℝ) := by
  change total (Fin.snoc half_21_03_φ2 (976227787/10000000000 : ℝ))=(3166405483/10000000000 : ℝ)
  rw [alternate_total_snoc,half_21_03_total2]
  norm_num

private theorem half_21_03_bounds3 : ∀ l,0≤half_21_03_φ3 l ∧ half_21_03_φ3 l≤1 ∧
    0≤shiftExponents 9 half_21_03_φ3 l :=
  alternate_bounds_snoc half_21_03_φ2 (976227787/10000000000 : ℝ) half_21_03_bounds2 (by norm_num)

private def half_21_03_φ4 : Fin 4 → ℝ := Fin.snoc half_21_03_φ3 (427099657/5000000000 : ℝ)

private theorem half_21_03_total4 : total half_21_03_φ4=(4020604797/10000000000 : ℝ) := by
  change total (Fin.snoc half_21_03_φ3 (427099657/5000000000 : ℝ))=(4020604797/10000000000 : ℝ)
  rw [alternate_total_snoc,half_21_03_total3]
  norm_num

private theorem half_21_03_bounds4 : ∀ l,0≤half_21_03_φ4 l ∧ half_21_03_φ4 l≤1 ∧
    0≤shiftExponents 9 half_21_03_φ4 l :=
  alternate_bounds_snoc half_21_03_φ3 (427099657/5000000000 : ℝ) half_21_03_bounds3 (by norm_num)

private def half_21_03_φ5 : Fin 5 → ℝ := Fin.snoc half_21_03_φ4 (1868561/25000000 : ℝ)

private theorem half_21_03_total5 : total half_21_03_φ5=(4768029197/10000000000 : ℝ) := by
  change total (Fin.snoc half_21_03_φ4 (1868561/25000000 : ℝ))=(4768029197/10000000000 : ℝ)
  rw [alternate_total_snoc,half_21_03_total4]
  norm_num

private theorem half_21_03_bounds5 : ∀ l,0≤half_21_03_φ5 l ∧ half_21_03_φ5 l≤1 ∧
    0≤shiftExponents 9 half_21_03_φ5 l :=
  alternate_bounds_snoc half_21_03_φ4 (1868561/25000000 : ℝ) half_21_03_bounds4 (by norm_num)

private def half_21_03_φ6 : Fin 6 → ℝ := Fin.snoc half_21_03_φ5 (13079927/200000000 : ℝ)

private theorem half_21_03_total6 : total half_21_03_φ6=(5422025547/10000000000 : ℝ) := by
  change total (Fin.snoc half_21_03_φ5 (13079927/200000000 : ℝ))=(5422025547/10000000000 : ℝ)
  rw [alternate_total_snoc,half_21_03_total5]
  norm_num

private theorem half_21_03_bounds6 : ∀ l,0≤half_21_03_φ6 l ∧ half_21_03_φ6 l≤1 ∧
    0≤shiftExponents 9 half_21_03_φ6 l :=
  alternate_bounds_snoc half_21_03_φ5 (13079927/200000000 : ℝ) half_21_03_bounds5 (by norm_num)

private theorem half_21_03_prefix : PrefixCondition 9 half_21_03_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_21_03_φ1, half_21_03_φ2, half_21_03_φ3, half_21_03_φ4, half_21_03_φ5, half_21_03_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_21_03_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_21_03_φ6) (8733923359/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_21_03_φ6
    (fun i => (half_21_03_bounds6 i).1) (fun i => (half_21_03_bounds6 i).2.1)
    (fun i => (half_21_03_bounds6 i).2.2) half_21_03_prefix
  convert h using 1 <;> norm_num [half_21_03_total1, half_21_03_total2, half_21_03_total3, half_21_03_total4, half_21_03_total5, half_21_03_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_21_03_hx6 : SourcePowerBound
    (powerBoxCross 9 15 64 half_21_03_φ6) (24928073447/2000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 15) (r := 2) (v := 0) (w := 20) (D := 64)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_21_03_φ6 (by norm_num [half_21_03_total1, half_21_03_total2, half_21_03_total3, half_21_03_total4, half_21_03_total5, half_21_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_21_03_total1, half_21_03_total2, half_21_03_total3, half_21_03_total4, half_21_03_total5, half_21_03_total6, parameterExponent, curveLoss, dyadicExponent]) half_21_03_hF2
    (admissibleExponent_zero 9) (half_20_03)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_21_03_total1, half_21_03_total2, half_21_03_total3, half_21_03_total4, half_21_03_total5, half_21_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_03_hx5 : SourcePowerBound
    (powerBoxCross 9 16 32 half_21_03_φ5) (28829795437/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 16) (u := 14) (t := 17)
    (D := 32) (ψ := (13079927/200000000 : ℝ)) half_21_03_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_03_bounds5 l).1) (fun l => (half_21_03_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_03_total1, half_21_03_total2, half_21_03_total3, half_21_03_total4, half_21_03_total5, half_21_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_03) (half_17_03)
    (by simpa only [half_21_03_φ6, show (2:ℝ)*32=64 by norm_num] using half_21_03_hx6)
  exact h.weaken (by norm_num [half_21_03_total1, half_21_03_total2, half_21_03_total3, half_21_03_total4, half_21_03_total5, half_21_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_03_hx4 : SourcePowerBound
    (powerBoxCross 9 17 16 half_21_03_φ4) (84619626909/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 17) (u := 15) (t := 18)
    (D := 16) (ψ := (1868561/25000000 : ℝ)) half_21_03_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_03_bounds4 l).1) (fun l => (half_21_03_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_03_total1, half_21_03_total2, half_21_03_total3, half_21_03_total4, half_21_03_total5, half_21_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_03) (half_18_03)
    (by simpa only [half_21_03_φ5, show (2:ℝ)*16=32 by norm_num] using half_21_03_hx5)
  exact h.weaken (by norm_num [half_21_03_total1, half_21_03_total2, half_21_03_total3, half_21_03_total4, half_21_03_total5, half_21_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_03_hx3 : SourcePowerBound
    (powerBoxCross 9 18 8 half_21_03_φ3) (100506322239/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 18) (u := 16) (t := 19)
    (D := 8) (ψ := (427099657/5000000000 : ℝ)) half_21_03_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_03_bounds3 l).1) (fun l => (half_21_03_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_03_total1, half_21_03_total2, half_21_03_total3, half_21_03_total4, half_21_03_total5, half_21_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_03) (half_19_03)
    (by simpa only [half_21_03_φ4, show (2:ℝ)*8=16 by norm_num] using half_21_03_hx4)
  exact h.weaken (by norm_num [half_21_03_total1, half_21_03_total2, half_21_03_total3, half_21_03_total4, half_21_03_total5, half_21_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_03_hx2 : SourcePowerBound
    (powerBoxCross 9 19 4 half_21_03_φ2) (120358661679/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 19) (u := 17) (t := 20)
    (D := 4) (ψ := (976227787/10000000000 : ℝ)) half_21_03_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_03_bounds2 l).1) (fun l => (half_21_03_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_03_total1, half_21_03_total2, half_21_03_total3, half_21_03_total4, half_21_03_total5, half_21_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_03) (half_20_03)
    (by simpa only [half_21_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_21_03_hx3)
  exact h.weaken (by norm_num [half_21_03_total1, half_21_03_total2, half_21_03_total3, half_21_03_total4, half_21_03_total5, half_21_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_03_hx1 : SourcePowerBound
    (powerBoxCross 9 20 2 half_21_03_φ1) (57738677413/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 20) (u := 18) (t := 21)
    (D := 2) (ψ := (43328001/400000000 : ℝ)) half_21_03_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_03_bounds1 l).1) (fun l => (half_21_03_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_03_total1, half_21_03_total2, half_21_03_total3, half_21_03_total4, half_21_03_total5, half_21_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_19_03) (chord_69)
    (by simpa only [half_21_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_21_03_hx2)
  exact h.weaken (by norm_num [half_21_03_total1, half_21_03_total2, half_21_03_total3, half_21_03_total4, half_21_03_total5, half_21_03_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_21_03 : AdmissibleExponent 9 42 (165932758117/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 19) (ψ := (1106977671/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_20_03)
    (by simpa only [half_21_03_φ1] using half_21_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_21_03_total1, half_21_03_total2, half_21_03_total3, half_21_03_total4, half_21_03_total5, half_21_03_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_22_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1111111111/10000000000 : ℝ)

private theorem half_22_03_total1 : total half_22_03_φ1=(1111111111/10000000000 : ℝ) := by
  norm_num [half_22_03_φ1,total,emptyPhi,Fin.snoc]

private theorem half_22_03_bounds1 : ∀ l,0≤half_22_03_φ1 l ∧ half_22_03_φ1 l≤1 ∧
    0≤shiftExponents 9 half_22_03_φ1 l :=
  alternate_bounds_snoc emptyPhi (1111111111/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_22_03_φ2 : Fin 2 → ℝ := Fin.snoc half_22_03_φ1 (1092530673/10000000000 : ℝ)

private theorem half_22_03_total2 : total half_22_03_φ2=(275455223/1250000000 : ℝ) := by
  change total (Fin.snoc half_22_03_φ1 (1092530673/10000000000 : ℝ))=(275455223/1250000000 : ℝ)
  rw [alternate_total_snoc,half_22_03_total1]
  norm_num

private theorem half_22_03_bounds2 : ∀ l,0≤half_22_03_φ2 l ∧ half_22_03_φ2 l≤1 ∧
    0≤shiftExponents 9 half_22_03_φ2 l :=
  alternate_bounds_snoc half_22_03_φ1 (1092530673/10000000000 : ℝ) half_22_03_bounds1 (by norm_num)

private def half_22_03_φ3 : Fin 3 → ℝ := Fin.snoc half_22_03_φ2 (121818097/1250000000 : ℝ)

private theorem half_22_03_total3 : total half_22_03_φ3=(9931833/31250000 : ℝ) := by
  change total (Fin.snoc half_22_03_φ2 (121818097/1250000000 : ℝ))=(9931833/31250000 : ℝ)
  rw [alternate_total_snoc,half_22_03_total2]
  norm_num

private theorem half_22_03_bounds3 : ∀ l,0≤half_22_03_φ3 l ∧ half_22_03_φ3 l≤1 ∧
    0≤shiftExponents 9 half_22_03_φ3 l :=
  alternate_bounds_snoc half_22_03_φ2 (121818097/1250000000 : ℝ) half_22_03_bounds2 (by norm_num)

private def half_22_03_φ4 : Fin 4 → ℝ := Fin.snoc half_22_03_φ3 (852726679/10000000000 : ℝ)

private theorem half_22_03_total4 : total half_22_03_φ4=(4030913239/10000000000 : ℝ) := by
  change total (Fin.snoc half_22_03_φ3 (852726679/10000000000 : ℝ))=(4030913239/10000000000 : ℝ)
  rw [alternate_total_snoc,half_22_03_total3]
  norm_num

private theorem half_22_03_bounds4 : ∀ l,0≤half_22_03_φ4 l ∧ half_22_03_φ4 l≤1 ∧
    0≤shiftExponents 9 half_22_03_φ4 l :=
  alternate_bounds_snoc half_22_03_φ3 (852726679/10000000000 : ℝ) half_22_03_bounds3 (by norm_num)

private def half_22_03_φ5 : Fin 5 → ℝ := Fin.snoc half_22_03_φ4 (186533961/2500000000 : ℝ)

private theorem half_22_03_total5 : total half_22_03_φ5=(4777049083/10000000000 : ℝ) := by
  change total (Fin.snoc half_22_03_φ4 (186533961/2500000000 : ℝ))=(4777049083/10000000000 : ℝ)
  rw [alternate_total_snoc,half_22_03_total4]
  norm_num

private theorem half_22_03_bounds5 : ∀ l,0≤half_22_03_φ5 l ∧ half_22_03_φ5 l≤1 ∧
    0≤shiftExponents 9 half_22_03_φ5 l :=
  alternate_bounds_snoc half_22_03_φ4 (186533961/2500000000 : ℝ) half_22_03_bounds4 (by norm_num)

private def half_22_03_φ6 : Fin 6 → ℝ := Fin.snoc half_22_03_φ5 (2550269/39062500 : ℝ)

private theorem half_22_03_total6 : total half_22_03_φ6=(5429917947/10000000000 : ℝ) := by
  change total (Fin.snoc half_22_03_φ5 (2550269/39062500 : ℝ))=(5429917947/10000000000 : ℝ)
  rw [alternate_total_snoc,half_22_03_total5]
  norm_num

private theorem half_22_03_bounds6 : ∀ l,0≤half_22_03_φ6 l ∧ half_22_03_φ6 l≤1 ∧
    0≤shiftExponents 9 half_22_03_φ6 l :=
  alternate_bounds_snoc half_22_03_φ5 (2550269/39062500 : ℝ) half_22_03_bounds5 (by norm_num)

private theorem half_22_03_prefix : PrefixCondition 9 half_22_03_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_22_03_φ1, half_22_03_φ2, half_22_03_φ3, half_22_03_φ4, half_22_03_φ5, half_22_03_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_22_03_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_22_03_φ6) (8710246159/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_22_03_φ6
    (fun i => (half_22_03_bounds6 i).1) (fun i => (half_22_03_bounds6 i).2.1)
    (fun i => (half_22_03_bounds6 i).2.2) half_22_03_prefix
  convert h using 1 <;> norm_num [half_22_03_total1, half_22_03_total2, half_22_03_total3, half_22_03_total4, half_22_03_total5, half_22_03_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_22_03_hx6 : SourcePowerBound
    (powerBoxCross 9 16 64 half_22_03_φ6) (133504912923/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 16) (r := 2) (v := 21) (w := 22) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_22_03_φ6 (by norm_num [half_22_03_total1, half_22_03_total2, half_22_03_total3, half_22_03_total4, half_22_03_total5, half_22_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_22_03_total1, half_22_03_total2, half_22_03_total3, half_22_03_total4, half_22_03_total5, half_22_03_total6, parameterExponent, curveLoss, dyadicExponent]) half_22_03_hF2
    (half_21_03) (half_22_02)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_22_03_total1, half_22_03_total2, half_22_03_total3, half_22_03_total4, half_22_03_total5, half_22_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_03_hx5 : SourcePowerBound
    (powerBoxCross 9 17 32 half_22_03_φ5) (154094883609/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 17) (u := 15) (t := 18)
    (D := 32) (ψ := (2550269/39062500 : ℝ)) half_22_03_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_03_bounds5 l).1) (fun l => (half_22_03_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_03_total1, half_22_03_total2, half_22_03_total3, half_22_03_total4, half_22_03_total5, half_22_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_03) (half_18_03)
    (by simpa only [half_22_03_φ6, show (2:ℝ)*32=64 by norm_num] using half_22_03_hx6)
  exact h.weaken (by norm_num [half_22_03_total1, half_22_03_total2, half_22_03_total3, half_22_03_total4, half_22_03_total5, half_22_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_03_hx4 : SourcePowerBound
    (powerBoxCross 9 18 16 half_22_03_φ4) (22569130193/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 18) (u := 16) (t := 19)
    (D := 16) (ψ := (186533961/2500000000 : ℝ)) half_22_03_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_03_bounds4 l).1) (fun l => (half_22_03_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_03_total1, half_22_03_total2, half_22_03_total3, half_22_03_total4, half_22_03_total5, half_22_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_03) (half_19_03)
    (by simpa only [half_22_03_φ5, show (2:ℝ)*16=32 by norm_num] using half_22_03_hx5)
  exact h.weaken (by norm_num [half_22_03_total1, half_22_03_total2, half_22_03_total3, half_22_03_total4, half_22_03_total5, half_22_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_03_hx3 : SourcePowerBound
    (powerBoxCross 9 19 8 half_22_03_φ3) (106977192173/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 19) (u := 17) (t := 20)
    (D := 8) (ψ := (852726679/10000000000 : ℝ)) half_22_03_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_03_bounds3 l).1) (fun l => (half_22_03_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_03_total1, half_22_03_total2, half_22_03_total3, half_22_03_total4, half_22_03_total5, half_22_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_03) (half_20_03)
    (by simpa only [half_22_03_φ4, show (2:ℝ)*8=16 by norm_num] using half_22_03_hx4)
  exact h.weaken (by norm_num [half_22_03_total1, half_22_03_total2, half_22_03_total3, half_22_03_total4, half_22_03_total5, half_22_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_03_hx2 : SourcePowerBound
    (powerBoxCross 9 20 4 half_22_03_φ2) (127779412799/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 20) (u := 18) (t := 21)
    (D := 4) (ψ := (121818097/1250000000 : ℝ)) half_22_03_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_03_bounds2 l).1) (fun l => (half_22_03_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_03_total1, half_22_03_total2, half_22_03_total3, half_22_03_total4, half_22_03_total5, half_22_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_19_03) (half_21_03)
    (by simpa only [half_22_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_22_03_hx3)
  exact h.weaken (by norm_num [half_22_03_total1, half_22_03_total2, half_22_03_total3, half_22_03_total4, half_22_03_total5, half_22_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_03_hx1 : SourcePowerBound
    (powerBoxCross 9 21 2 half_22_03_φ1) (153110085511/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 21) (u := 19) (t := 22)
    (D := 2) (ψ := (1092530673/10000000000 : ℝ)) half_22_03_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_03_bounds1 l).1) (fun l => (half_22_03_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_03_total1, half_22_03_total2, half_22_03_total3, half_22_03_total4, half_22_03_total5, half_22_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_20_03) (half_22_02)
    (by simpa only [half_22_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_22_03_hx2)
  exact h.weaken (by norm_num [half_22_03_total1, half_22_03_total2, half_22_03_total3, half_22_03_total4, half_22_03_total5, half_22_03_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_22_03 : AdmissibleExponent 9 44 (351775726573/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 20) (ψ := (1111111111/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_21_03)
    (by simpa only [half_22_03_φ1] using half_22_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_22_03_total1, half_22_03_total2, half_22_03_total3, half_22_03_total4, half_22_03_total5, half_22_03_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_10_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (35355849/400000000 : ℝ)

private theorem half_10_04_total1 : total half_10_04_φ1=(35355849/400000000 : ℝ) := by
  norm_num [half_10_04_φ1,total,emptyPhi,Fin.snoc]

private theorem half_10_04_bounds1 : ∀ l,0≤half_10_04_φ1 l ∧ half_10_04_φ1 l≤1 ∧
    0≤shiftExponents 9 half_10_04_φ1 l :=
  alternate_bounds_snoc emptyPhi (35355849/400000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_10_04_φ2 : Fin 2 → ℝ := Fin.snoc half_10_04_φ1 (102702629/1250000000 : ℝ)

private theorem half_10_04_total2 : total half_10_04_φ2=(1705517257/10000000000 : ℝ) := by
  change total (Fin.snoc half_10_04_φ1 (102702629/1250000000 : ℝ))=(1705517257/10000000000 : ℝ)
  rw [alternate_total_snoc,half_10_04_total1]
  norm_num

private theorem half_10_04_bounds2 : ∀ l,0≤half_10_04_φ2 l ∧ half_10_04_φ2 l≤1 ∧
    0≤shiftExponents 9 half_10_04_φ2 l :=
  alternate_bounds_snoc half_10_04_φ1 (102702629/1250000000 : ℝ) half_10_04_bounds1 (by norm_num)

private def half_10_04_φ3 : Fin 3 → ℝ := Fin.snoc half_10_04_φ2 (717250031/10000000000 : ℝ)

private theorem half_10_04_total3 : total half_10_04_φ3=(302845911/1250000000 : ℝ) := by
  change total (Fin.snoc half_10_04_φ2 (717250031/10000000000 : ℝ))=(302845911/1250000000 : ℝ)
  rw [alternate_total_snoc,half_10_04_total2]
  norm_num

private theorem half_10_04_bounds3 : ∀ l,0≤half_10_04_φ3 l ∧ half_10_04_φ3 l≤1 ∧
    0≤shiftExponents 9 half_10_04_φ3 l :=
  alternate_bounds_snoc half_10_04_φ2 (717250031/10000000000 : ℝ) half_10_04_bounds2 (by norm_num)

private def half_10_04_φ4 : Fin 4 → ℝ := Fin.snoc half_10_04_φ3 (225476219/5000000000 : ℝ)

private theorem half_10_04_total4 : total half_10_04_φ4=(1436859863/5000000000 : ℝ) := by
  change total (Fin.snoc half_10_04_φ3 (225476219/5000000000 : ℝ))=(1436859863/5000000000 : ℝ)
  rw [alternate_total_snoc,half_10_04_total3]
  norm_num

private theorem half_10_04_bounds4 : ∀ l,0≤half_10_04_φ4 l ∧ half_10_04_φ4 l≤1 ∧
    0≤shiftExponents 9 half_10_04_φ4 l :=
  alternate_bounds_snoc half_10_04_φ3 (225476219/5000000000 : ℝ) half_10_04_bounds3 (by norm_num)

private theorem half_10_04_prefix : PrefixCondition 9 half_10_04_φ4 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_10_04_φ1, half_10_04_φ2, half_10_04_φ3, half_10_04_φ4, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_10_04_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 16 half_10_04_φ4) (4439420411/625000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 9) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_04_φ4
    (fun i => (half_10_04_bounds4 i).1) (fun i => (half_10_04_bounds4 i).2.1)
    (fun i => (half_10_04_bounds4 i).2.2) half_10_04_prefix
  convert h using 1 <;> norm_num [half_10_04_total1, half_10_04_total2, half_10_04_total3, half_10_04_total4, parameterExponent, curveLoss, dyadicExponent]

private theorem half_10_04_hx4 : SourcePowerBound
    (powerBoxCross 9 6 16 half_10_04_φ4) (69087888297/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 6) (r := 2) (v := 0) (w := 8) (D := 16)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_10_04_φ4 (by norm_num [half_10_04_total1, half_10_04_total2, half_10_04_total3, half_10_04_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_10_04_total1, half_10_04_total2, half_10_04_total3, half_10_04_total4, parameterExponent, curveLoss, dyadicExponent]) half_10_04_hF2
    (admissibleExponent_zero 9) (SeedCompletionHigher9SimpleSeeds.degree9_half_8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_04_total1, half_10_04_total2, half_10_04_total3, half_10_04_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_10_04_hx3 : SourcePowerBound
    (powerBoxCross 9 7 8 half_10_04_φ3) (78718708323/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 7) (u := 5) (t := 8)
    (D := 8) (ψ := (225476219/5000000000 : ℝ)) half_10_04_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_10_04_bounds3 l).1) (fun l => (half_10_04_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_10_04_total1, half_10_04_total2, half_10_04_total3, half_10_04_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_6) (SeedCompletionHigher9SimpleSeeds.degree9_half_8)
    (by simpa only [half_10_04_φ4, show (2:ℝ)*8=16 by norm_num] using half_10_04_hx4)
  exact h.weaken (by norm_num [half_10_04_total1, half_10_04_total2, half_10_04_total3, half_10_04_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_10_04_hx2 : SourcePowerBound
    (powerBoxCross 9 8 4 half_10_04_φ2) (93410058007/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (717250031/10000000000 : ℝ)) half_10_04_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_10_04_bounds2 l).1) (fun l => (half_10_04_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_10_04_total1, half_10_04_total2, half_10_04_total3, half_10_04_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_7) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_10_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_04_hx3)
  exact h.weaken (by norm_num [half_10_04_total1, half_10_04_total2, half_10_04_total3, half_10_04_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_10_04_hx1 : SourcePowerBound
    (powerBoxCross 9 9 2 half_10_04_φ1) (56230053021/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (102702629/1250000000 : ℝ)) half_10_04_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_10_04_bounds1 l).1) (fun l => (half_10_04_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_10_04_total1, half_10_04_total2, half_10_04_total3, half_10_04_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_03)
    (by simpa only [half_10_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_04_hx2)
  exact h.weaken (by norm_num [half_10_04_total1, half_10_04_total2, half_10_04_total3, half_10_04_total4, parameterExponent, curveLoss, dyadicExponent])

theorem half_10_04 : AdmissibleExponent 9 20 (127486341867/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 8) (ψ := (35355849/400000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_10_04_φ1] using half_10_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_04_total1, half_10_04_total2, half_10_04_total3, half_10_04_total4, parameterExponent, curveLoss, dyadicExponent])

private def half_11_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (922927751/10000000000 : ℝ)

private theorem half_11_04_total1 : total half_11_04_φ1=(922927751/10000000000 : ℝ) := by
  norm_num [half_11_04_φ1,total,emptyPhi,Fin.snoc]

private theorem half_11_04_bounds1 : ∀ l,0≤half_11_04_φ1 l ∧ half_11_04_φ1 l≤1 ∧
    0≤shiftExponents 9 half_11_04_φ1 l :=
  alternate_bounds_snoc emptyPhi (922927751/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_11_04_φ2 : Fin 2 → ℝ := Fin.snoc half_11_04_φ1 (216663091/2500000000 : ℝ)

private theorem half_11_04_total2 : total half_11_04_φ2=(357916023/2000000000 : ℝ) := by
  change total (Fin.snoc half_11_04_φ1 (216663091/2500000000 : ℝ))=(357916023/2000000000 : ℝ)
  rw [alternate_total_snoc,half_11_04_total1]
  norm_num

private theorem half_11_04_bounds2 : ∀ l,0≤half_11_04_φ2 l ∧ half_11_04_φ2 l≤1 ∧
    0≤shiftExponents 9 half_11_04_φ2 l :=
  alternate_bounds_snoc half_11_04_φ1 (216663091/2500000000 : ℝ) half_11_04_bounds1 (by norm_num)

private def half_11_04_φ3 : Fin 3 → ℝ := Fin.snoc half_11_04_φ2 (98597201/1250000000 : ℝ)

private theorem half_11_04_total3 : total half_11_04_φ3=(2578357723/10000000000 : ℝ) := by
  change total (Fin.snoc half_11_04_φ2 (98597201/1250000000 : ℝ))=(2578357723/10000000000 : ℝ)
  rw [alternate_total_snoc,half_11_04_total2]
  norm_num

private theorem half_11_04_bounds3 : ∀ l,0≤half_11_04_φ3 l ∧ half_11_04_φ3 l≤1 ∧
    0≤shiftExponents 9 half_11_04_φ3 l :=
  alternate_bounds_snoc half_11_04_φ2 (98597201/1250000000 : ℝ) half_11_04_bounds2 (by norm_num)

private def half_11_04_φ4 : Fin 4 → ℝ := Fin.snoc half_11_04_φ3 (313450847/5000000000 : ℝ)

private theorem half_11_04_total4 : total half_11_04_φ4=(3205259417/10000000000 : ℝ) := by
  change total (Fin.snoc half_11_04_φ3 (313450847/5000000000 : ℝ))=(3205259417/10000000000 : ℝ)
  rw [alternate_total_snoc,half_11_04_total3]
  norm_num

private theorem half_11_04_bounds4 : ∀ l,0≤half_11_04_φ4 l ∧ half_11_04_φ4 l≤1 ∧
    0≤shiftExponents 9 half_11_04_φ4 l :=
  alternate_bounds_snoc half_11_04_φ3 (313450847/5000000000 : ℝ) half_11_04_bounds3 (by norm_num)

private theorem half_11_04_prefix : PrefixCondition 9 half_11_04_φ4 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_11_04_φ1, half_11_04_φ2, half_11_04_φ3, half_11_04_φ4, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_11_04_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 16 half_11_04_φ4) (7884221749/1250000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 9) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_04_φ4
    (fun i => (half_11_04_bounds4 i).1) (fun i => (half_11_04_bounds4 i).2.1)
    (fun i => (half_11_04_bounds4 i).2.2) half_11_04_prefix
  convert h using 1 <;> norm_num [half_11_04_total1, half_11_04_total2, half_11_04_total3, half_11_04_total4, parameterExponent, curveLoss, dyadicExponent]

private theorem half_11_04_hx4 : SourcePowerBound
    (powerBoxCross 9 7 16 half_11_04_φ4) (60223653/8000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 7) (r := 2) (v := 9) (w := 10) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_11_04_φ4 (by norm_num [half_11_04_total1, half_11_04_total2, half_11_04_total3, half_11_04_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_11_04_total1, half_11_04_total2, half_11_04_total3, half_11_04_total4, parameterExponent, curveLoss, dyadicExponent]) half_11_04_hF2
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_10_04)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_04_total1, half_11_04_total2, half_11_04_total3, half_11_04_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_11_04_hx3 : SourcePowerBound
    (powerBoxCross 9 8 8 half_11_04_φ3) (17549809469/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (313450847/5000000000 : ℝ)) half_11_04_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_11_04_bounds3 l).1) (fun l => (half_11_04_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_11_04_total1, half_11_04_total2, half_11_04_total3, half_11_04_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_7) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_11_04_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_04_hx4)
  exact h.weaken (by norm_num [half_11_04_total1, half_11_04_total2, half_11_04_total3, half_11_04_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_11_04_hx2 : SourcePowerBound
    (powerBoxCross 9 9 4 half_11_04_φ2) (10496785509/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (98597201/1250000000 : ℝ)) half_11_04_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_11_04_bounds2 l).1) (fun l => (half_11_04_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_11_04_total1, half_11_04_total2, half_11_04_total3, half_11_04_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_04)
    (by simpa only [half_11_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_04_hx3)
  exact h.weaken (by norm_num [half_11_04_total1, half_11_04_total2, half_11_04_total3, half_11_04_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_11_04_hx1 : SourcePowerBound
    (powerBoxCross 9 10 2 half_11_04_φ1) (126643201347/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (216663091/2500000000 : ℝ)) half_11_04_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_11_04_bounds1 l).1) (fun l => (half_11_04_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_11_04_total1, half_11_04_total2, half_11_04_total3, half_11_04_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_03)
    (by simpa only [half_11_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_04_hx2)
  exact h.weaken (by norm_num [half_11_04_total1, half_11_04_total2, half_11_04_total3, half_11_04_total4, parameterExponent, curveLoss, dyadicExponent])

theorem half_11_04 : AdmissibleExponent 9 22 (18022353577/1250000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 9) (ψ := (922927751/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_10_04)
    (by simpa only [half_11_04_φ1] using half_11_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_04_total1, half_11_04_total2, half_11_04_total3, half_11_04_total4, parameterExponent, curveLoss, dyadicExponent])

private def half_12_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (956061037/10000000000 : ℝ)

private theorem half_12_04_total1 : total half_12_04_φ1=(956061037/10000000000 : ℝ) := by
  norm_num [half_12_04_φ1,total,emptyPhi,Fin.snoc]

private theorem half_12_04_bounds1 : ∀ l,0≤half_12_04_φ1 l ∧ half_12_04_φ1 l≤1 ∧
    0≤shiftExponents 9 half_12_04_φ1 l :=
  alternate_bounds_snoc emptyPhi (956061037/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_12_04_φ2 : Fin 2 → ℝ := Fin.snoc half_12_04_φ1 (22621089/250000000 : ℝ)

private theorem half_12_04_total2 : total half_12_04_φ2=(1860904597/10000000000 : ℝ) := by
  change total (Fin.snoc half_12_04_φ1 (22621089/250000000 : ℝ))=(1860904597/10000000000 : ℝ)
  rw [alternate_total_snoc,half_12_04_total1]
  norm_num

private theorem half_12_04_bounds2 : ∀ l,0≤half_12_04_φ2 l ∧ half_12_04_φ2 l≤1 ∧
    0≤shiftExponents 9 half_12_04_φ2 l :=
  alternate_bounds_snoc half_12_04_φ1 (22621089/250000000 : ℝ) half_12_04_bounds1 (by norm_num)

private def half_12_04_φ3 : Fin 3 → ℝ := Fin.snoc half_12_04_φ2 (210480147/2500000000 : ℝ)

private theorem half_12_04_total3 : total half_12_04_φ3=(540565037/2000000000 : ℝ) := by
  change total (Fin.snoc half_12_04_φ2 (210480147/2500000000 : ℝ))=(540565037/2000000000 : ℝ)
  rw [alternate_total_snoc,half_12_04_total2]
  norm_num

private theorem half_12_04_bounds3 : ∀ l,0≤half_12_04_φ3 l ∧ half_12_04_φ3 l≤1 ∧
    0≤shiftExponents 9 half_12_04_φ3 l :=
  alternate_bounds_snoc half_12_04_φ2 (210480147/2500000000 : ℝ) half_12_04_bounds2 (by norm_num)

private def half_12_04_φ4 : Fin 4 → ℝ := Fin.snoc half_12_04_φ3 (728822577/10000000000 : ℝ)

private theorem half_12_04_total4 : total half_12_04_φ4=(1715823881/5000000000 : ℝ) := by
  change total (Fin.snoc half_12_04_φ3 (728822577/10000000000 : ℝ))=(1715823881/5000000000 : ℝ)
  rw [alternate_total_snoc,half_12_04_total3]
  norm_num

private theorem half_12_04_bounds4 : ∀ l,0≤half_12_04_φ4 l ∧ half_12_04_φ4 l≤1 ∧
    0≤shiftExponents 9 half_12_04_φ4 l :=
  alternate_bounds_snoc half_12_04_φ3 (728822577/10000000000 : ℝ) half_12_04_bounds3 (by norm_num)

private def half_12_04_φ5 : Fin 5 → ℝ := Fin.snoc half_12_04_φ4 (45310307/1000000000 : ℝ)

private theorem half_12_04_total5 : total half_12_04_φ5=(242796927/625000000 : ℝ) := by
  change total (Fin.snoc half_12_04_φ4 (45310307/1000000000 : ℝ))=(242796927/625000000 : ℝ)
  rw [alternate_total_snoc,half_12_04_total4]
  norm_num

private theorem half_12_04_bounds5 : ∀ l,0≤half_12_04_φ5 l ∧ half_12_04_φ5 l≤1 ∧
    0≤shiftExponents 9 half_12_04_φ5 l :=
  alternate_bounds_snoc half_12_04_φ4 (45310307/1000000000 : ℝ) half_12_04_bounds4 (by norm_num)

private theorem half_12_04_prefix : PrefixCondition 9 half_12_04_φ5 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_12_04_φ1, half_12_04_φ2, half_12_04_φ3, half_12_04_φ4, half_12_04_φ5, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_12_04_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 32 half_12_04_φ5) (599734219/78125000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_12_04_φ5
    (fun i => (half_12_04_bounds5 i).1) (fun i => (half_12_04_bounds5 i).2.1)
    (fun i => (half_12_04_bounds5 i).2.2) half_12_04_prefix
  convert h using 1 <;> norm_num [half_12_04_total1, half_12_04_total2, half_12_04_total3, half_12_04_total4, half_12_04_total5, parameterExponent, curveLoss, dyadicExponent]

private theorem half_12_04_hx5 : SourcePowerBound
    (powerBoxCross 9 7 32 half_12_04_φ5) (18187838367/2500000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 7) (r := 2) (v := 9) (w := 10) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_12_04_φ5 (by norm_num [half_12_04_total1, half_12_04_total2, half_12_04_total3, half_12_04_total4, half_12_04_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_12_04_total1, half_12_04_total2, half_12_04_total3, half_12_04_total4, half_12_04_total5, parameterExponent, curveLoss, dyadicExponent]) half_12_04_hF2
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_10_04)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_04_total1, half_12_04_total2, half_12_04_total3, half_12_04_total4, half_12_04_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_04_hx4 : SourcePowerBound
    (powerBoxCross 9 8 16 half_12_04_φ4) (82188196513/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 8) (u := 6) (t := 9)
    (D := 16) (ψ := (45310307/1000000000 : ℝ)) half_12_04_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_04_bounds4 l).1) (fun l => (half_12_04_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_04_total1, half_12_04_total2, half_12_04_total3, half_12_04_total4, half_12_04_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_7) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_12_04_φ5, show (2:ℝ)*16=32 by norm_num] using half_12_04_hx5)
  exact h.weaken (by norm_num [half_12_04_total1, half_12_04_total2, half_12_04_total3, half_12_04_total4, half_12_04_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_04_hx3 : SourcePowerBound
    (powerBoxCross 9 9 8 half_12_04_φ3) (97263473001/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (728822577/10000000000 : ℝ)) half_12_04_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_04_bounds3 l).1) (fun l => (half_12_04_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_04_total1, half_12_04_total2, half_12_04_total3, half_12_04_total4, half_12_04_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_04)
    (by simpa only [half_12_04_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_04_hx4)
  exact h.weaken (by norm_num [half_12_04_total1, half_12_04_total2, half_12_04_total3, half_12_04_total4, half_12_04_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_04_hx2 : SourcePowerBound
    (powerBoxCross 9 10 4 half_12_04_φ2) (117018705171/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (210480147/2500000000 : ℝ)) half_12_04_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_04_bounds2 l).1) (fun l => (half_12_04_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_04_total1, half_12_04_total2, half_12_04_total3, half_12_04_total4, half_12_04_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_04)
    (by simpa only [half_12_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_04_hx3)
  exact h.weaken (by norm_num [half_12_04_total1, half_12_04_total2, half_12_04_total3, half_12_04_total4, half_12_04_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_04_hx1 : SourcePowerBound
    (powerBoxCross 9 11 2 half_12_04_φ1) (70675256809/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (22621089/250000000 : ℝ)) half_12_04_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_04_bounds1 l).1) (fun l => (half_12_04_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_04_total1, half_12_04_total2, half_12_04_total3, half_12_04_total4, half_12_04_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_04) (half_12_03)
    (by simpa only [half_12_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_04_hx2)
  exact h.weaken (by norm_num [half_12_04_total1, half_12_04_total2, half_12_04_total3, half_12_04_total4, half_12_04_total5, parameterExponent, curveLoss, dyadicExponent])

theorem half_12_04 : AdmissibleExponent 9 24 (32285559079/2000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 10) (ψ := (956061037/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_11_04)
    (by simpa only [half_12_04_φ1] using half_12_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_04_total1, half_12_04_total2, half_12_04_total3, half_12_04_total4, half_12_04_total5, parameterExponent, curveLoss, dyadicExponent])

private def half_13_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (984673349/10000000000 : ℝ)

private theorem half_13_04_total1 : total half_13_04_φ1=(984673349/10000000000 : ℝ) := by
  norm_num [half_13_04_φ1,total,emptyPhi,Fin.snoc]

private theorem half_13_04_bounds1 : ∀ l,0≤half_13_04_φ1 l ∧ half_13_04_φ1 l≤1 ∧
    0≤shiftExponents 9 half_13_04_φ1 l :=
  alternate_bounds_snoc emptyPhi (984673349/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_13_04_φ2 : Fin 2 → ℝ := Fin.snoc half_13_04_φ1 (37474439/400000000 : ℝ)

private theorem half_13_04_total2 : total half_13_04_φ2=(480383581/2500000000 : ℝ) := by
  change total (Fin.snoc half_13_04_φ1 (37474439/400000000 : ℝ))=(480383581/2500000000 : ℝ)
  rw [alternate_total_snoc,half_13_04_total1]
  norm_num

private theorem half_13_04_bounds2 : ∀ l,0≤half_13_04_φ2 l ∧ half_13_04_φ2 l≤1 ∧
    0≤shiftExponents 9 half_13_04_φ2 l :=
  alternate_bounds_snoc half_13_04_φ1 (37474439/400000000 : ℝ) half_13_04_bounds1 (by norm_num)

private def half_13_04_φ3 : Fin 3 → ℝ := Fin.snoc half_13_04_φ2 (221128931/2500000000 : ℝ)

private theorem half_13_04_total3 : total half_13_04_φ3=(10961133/39062500 : ℝ) := by
  change total (Fin.snoc half_13_04_φ2 (221128931/2500000000 : ℝ))=(10961133/39062500 : ℝ)
  rw [alternate_total_snoc,half_13_04_total2]
  norm_num

private theorem half_13_04_bounds3 : ∀ l,0≤half_13_04_φ3 l ∧ half_13_04_φ3 l≤1 ∧
    0≤shiftExponents 9 half_13_04_φ3 l :=
  alternate_bounds_snoc half_13_04_φ2 (221128931/2500000000 : ℝ) half_13_04_bounds2 (by norm_num)

private def half_13_04_φ4 : Fin 4 → ℝ := Fin.snoc half_13_04_φ3 (797261987/10000000000 : ℝ)

private theorem half_13_04_total4 : total half_13_04_φ4=(720662407/2000000000 : ℝ) := by
  change total (Fin.snoc half_13_04_φ3 (797261987/10000000000 : ℝ))=(720662407/2000000000 : ℝ)
  rw [alternate_total_snoc,half_13_04_total3]
  norm_num

private theorem half_13_04_bounds4 : ∀ l,0≤half_13_04_φ4 l ∧ half_13_04_φ4 l≤1 ∧
    0≤shiftExponents 9 half_13_04_φ4 l :=
  alternate_bounds_snoc half_13_04_φ3 (797261987/10000000000 : ℝ) half_13_04_bounds3 (by norm_num)

private def half_13_04_φ5 : Fin 5 → ℝ := Fin.snoc half_13_04_φ4 (612654189/10000000000 : ℝ)

private theorem half_13_04_total5 : total half_13_04_φ5=(263497889/625000000 : ℝ) := by
  change total (Fin.snoc half_13_04_φ4 (612654189/10000000000 : ℝ))=(263497889/625000000 : ℝ)
  rw [alternate_total_snoc,half_13_04_total4]
  norm_num

private theorem half_13_04_bounds5 : ∀ l,0≤half_13_04_φ5 l ∧ half_13_04_φ5 l≤1 ∧
    0≤shiftExponents 9 half_13_04_φ5 l :=
  alternate_bounds_snoc half_13_04_φ4 (612654189/10000000000 : ℝ) half_13_04_bounds4 (by norm_num)

private theorem half_13_04_prefix : PrefixCondition 9 half_13_04_φ5 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_13_04_φ1, half_13_04_φ2, half_13_04_φ3, half_13_04_φ4, half_13_04_φ5, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_13_04_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 32 half_13_04_φ5) (537631333/78125000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_13_04_φ5
    (fun i => (half_13_04_bounds5 i).1) (fun i => (half_13_04_bounds5 i).2.1)
    (fun i => (half_13_04_bounds5 i).2.2) half_13_04_prefix
  convert h using 1 <;> norm_num [half_13_04_total1, half_13_04_total2, half_13_04_total3, half_13_04_total4, half_13_04_total5, parameterExponent, curveLoss, dyadicExponent]

private theorem half_13_04_hx5 : SourcePowerBound
    (powerBoxCross 9 8 32 half_13_04_φ5) (15467119213/2000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 8) (r := 2) (v := 10) (w := 11) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_13_04_φ5 (by norm_num [half_13_04_total1, half_13_04_total2, half_13_04_total3, half_13_04_total4, half_13_04_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_13_04_total1, half_13_04_total2, half_13_04_total3, half_13_04_total4, half_13_04_total5, parameterExponent, curveLoss, dyadicExponent]) half_13_04_hF2
    (half_10_04) (half_11_04)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_04_total1, half_13_04_total2, half_13_04_total3, half_13_04_total4, half_13_04_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_04_hx4 : SourcePowerBound
    (powerBoxCross 9 9 16 half_13_04_φ4) (89623973747/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (612654189/10000000000 : ℝ)) half_13_04_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_04_bounds4 l).1) (fun l => (half_13_04_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_04_total1, half_13_04_total2, half_13_04_total3, half_13_04_total4, half_13_04_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_04)
    (by simpa only [half_13_04_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_04_hx5)
  exact h.weaken (by norm_num [half_13_04_total1, half_13_04_total2, half_13_04_total3, half_13_04_total4, half_13_04_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_04_hx3 : SourcePowerBound
    (powerBoxCross 9 10 8 half_13_04_φ3) (13403159679/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (797261987/10000000000 : ℝ)) half_13_04_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_04_bounds3 l).1) (fun l => (half_13_04_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_04_total1, half_13_04_total2, half_13_04_total3, half_13_04_total4, half_13_04_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_04)
    (by simpa only [half_13_04_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_04_hx4)
  exact h.weaken (by norm_num [half_13_04_total1, half_13_04_total2, half_13_04_total3, half_13_04_total4, half_13_04_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_04_hx2 : SourcePowerBound
    (powerBoxCross 9 11 4 half_13_04_φ2) (129533846011/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (221128931/2500000000 : ℝ)) half_13_04_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_04_bounds2 l).1) (fun l => (half_13_04_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_04_total1, half_13_04_total2, half_13_04_total3, half_13_04_total4, half_13_04_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_04) (half_12_04)
    (by simpa only [half_13_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_04_hx3)
  exact h.weaken (by norm_num [half_13_04_total1, half_13_04_total2, half_13_04_total3, half_13_04_total4, half_13_04_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_04_hx1 : SourcePowerBound
    (powerBoxCross 9 12 2 half_13_04_φ1) (39129275991/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (37474439/400000000 : ℝ)) half_13_04_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_04_bounds1 l).1) (fun l => (half_13_04_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_04_total1, half_13_04_total2, half_13_04_total3, half_13_04_total4, half_13_04_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_04) (half_13_03)
    (by simpa only [half_13_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_04_hx2)
  exact h.weaken (by norm_num [half_13_04_total1, half_13_04_total2, half_13_04_total3, half_13_04_total4, half_13_04_total5, parameterExponent, curveLoss, dyadicExponent])

theorem half_13_04 : AdmissibleExponent 9 26 (179164590991/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 11) (ψ := (984673349/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_12_04)
    (by simpa only [half_13_04_φ1] using half_13_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_04_total1, half_13_04_total2, half_13_04_total3, half_13_04_total4, half_13_04_total5, parameterExponent, curveLoss, dyadicExponent])

private def half_14_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (252213809/2500000000 : ℝ)

private theorem half_14_04_total1 : total half_14_04_φ1=(252213809/2500000000 : ℝ) := by
  norm_num [half_14_04_φ1,total,emptyPhi,Fin.snoc]

private theorem half_14_04_bounds1 : ∀ l,0≤half_14_04_φ1 l ∧ half_14_04_φ1 l≤1 ∧
    0≤shiftExponents 9 half_14_04_φ1 l :=
  alternate_bounds_snoc emptyPhi (252213809/2500000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_14_04_φ2 : Fin 2 → ℝ := Fin.snoc half_14_04_φ1 (1544953/16000000 : ℝ)

private theorem half_14_04_total2 : total half_14_04_φ2=(1974450861/10000000000 : ℝ) := by
  change total (Fin.snoc half_14_04_φ1 (1544953/16000000 : ℝ))=(1974450861/10000000000 : ℝ)
  rw [alternate_total_snoc,half_14_04_total1]
  norm_num

private theorem half_14_04_bounds2 : ∀ l,0≤half_14_04_φ2 l ∧ half_14_04_φ2 l≤1 ∧
    0≤shiftExponents 9 half_14_04_φ2 l :=
  alternate_bounds_snoc half_14_04_φ1 (1544953/16000000 : ℝ) half_14_04_bounds1 (by norm_num)

private def half_14_04_φ3 : Fin 3 → ℝ := Fin.snoc half_14_04_φ2 (28806317/312500000 : ℝ)

private theorem half_14_04_total3 : total half_14_04_φ3=(579250601/2000000000 : ℝ) := by
  change total (Fin.snoc half_14_04_φ2 (28806317/312500000 : ℝ))=(579250601/2000000000 : ℝ)
  rw [alternate_total_snoc,half_14_04_total2]
  norm_num

private theorem half_14_04_bounds3 : ∀ l,0≤half_14_04_φ3 l ∧ half_14_04_φ3 l≤1 ∧
    0≤shiftExponents 9 half_14_04_φ3 l :=
  alternate_bounds_snoc half_14_04_φ2 (28806317/312500000 : ℝ) half_14_04_bounds2 (by norm_num)

private def half_14_04_φ4 : Fin 4 → ℝ := Fin.snoc half_14_04_φ3 (854615451/10000000000 : ℝ)

private theorem half_14_04_total4 : total half_14_04_φ4=(468858557/1250000000 : ℝ) := by
  change total (Fin.snoc half_14_04_φ3 (854615451/10000000000 : ℝ))=(468858557/1250000000 : ℝ)
  rw [alternate_total_snoc,half_14_04_total3]
  norm_num

private theorem half_14_04_bounds4 : ∀ l,0≤half_14_04_φ4 l ∧ half_14_04_φ4 l≤1 ∧
    0≤shiftExponents 9 half_14_04_φ4 l :=
  alternate_bounds_snoc half_14_04_φ3 (854615451/10000000000 : ℝ) half_14_04_bounds3 (by norm_num)

private def half_14_04_φ5 : Fin 5 → ℝ := Fin.snoc half_14_04_φ4 (181868507/2500000000 : ℝ)

private theorem half_14_04_total5 : total half_14_04_φ5=(1119585621/2500000000 : ℝ) := by
  change total (Fin.snoc half_14_04_φ4 (181868507/2500000000 : ℝ))=(1119585621/2500000000 : ℝ)
  rw [alternate_total_snoc,half_14_04_total4]
  norm_num

private theorem half_14_04_bounds5 : ∀ l,0≤half_14_04_φ5 l ∧ half_14_04_φ5 l≤1 ∧
    0≤shiftExponents 9 half_14_04_φ5 l :=
  alternate_bounds_snoc half_14_04_φ4 (181868507/2500000000 : ℝ) half_14_04_bounds4 (by norm_num)

private def half_14_04_φ6 : Fin 6 → ℝ := Fin.snoc half_14_04_φ5 (212748607/5000000000 : ℝ)

private theorem half_14_04_total6 : total half_14_04_φ6=(2451919849/5000000000 : ℝ) := by
  change total (Fin.snoc half_14_04_φ5 (212748607/5000000000 : ℝ))=(2451919849/5000000000 : ℝ)
  rw [alternate_total_snoc,half_14_04_total5]
  norm_num

private theorem half_14_04_bounds6 : ∀ l,0≤half_14_04_φ6 l ∧ half_14_04_φ6 l≤1 ∧
    0≤shiftExponents 9 half_14_04_φ6 l :=
  alternate_bounds_snoc half_14_04_φ5 (212748607/5000000000 : ℝ) half_14_04_bounds5 (by norm_num)

private theorem half_14_04_prefix : PrefixCondition 9 half_14_04_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_14_04_φ1, half_14_04_φ2, half_14_04_φ3, half_14_04_φ4, half_14_04_φ5, half_14_04_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_14_04_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_14_04_φ6) (5144240453/625000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_14_04_φ6
    (fun i => (half_14_04_bounds6 i).1) (fun i => (half_14_04_bounds6 i).2.1)
    (fun i => (half_14_04_bounds6 i).2.2) half_14_04_prefix
  convert h using 1 <;> norm_num [half_14_04_total1, half_14_04_total2, half_14_04_total3, half_14_04_total4, half_14_04_total5, half_14_04_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_14_04_hF1 : SourcePowerBound
    (paddedMoment 9 0 1 64 half_14_04_φ6) (1923080151/625000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_14_04_φ6
    (fun i => (half_14_04_bounds6 i).1) (fun i => (half_14_04_bounds6 i).2.1)
    (fun i => (half_14_04_bounds6 i).2.2) half_14_04_prefix
  convert h using 1 <;> norm_num [half_14_04_total1, half_14_04_total2, half_14_04_total3, half_14_04_total4, half_14_04_total5, half_14_04_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_14_04_hx6 : SourcePowerBound
    (powerBoxCross 9 8 64 half_14_04_φ6) (73541908869/10000000000 : ℝ) := by
  have h := full_B_cross_power (k := 9) (s := 8) (r := 1) (v := 2) (t := 11) (D := 64)
    (a := (1/22 : ℝ)) (b := (5/22 : ℝ)) (c := (8/11 : ℝ))
    (by norm_num) half_14_04_φ6 (by norm_num [half_14_04_total1, half_14_04_total2, half_14_04_total3, half_14_04_total4, half_14_04_total5, half_14_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_14_04_total1, half_14_04_total2, half_14_04_total3, half_14_04_total4, half_14_04_total5, half_14_04_total6, parameterExponent, curveLoss, dyadicExponent]) half_14_04_hF1 half_14_04_hF2
    (half_11_04)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_04_total1, half_14_04_total2, half_14_04_total3, half_14_04_total4, half_14_04_total5, half_14_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_04_hx5 : SourcePowerBound
    (powerBoxCross 9 9 32 half_14_04_φ5) (20561402373/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 9) (u := 7) (t := 10)
    (D := 32) (ψ := (212748607/5000000000 : ℝ)) half_14_04_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_04_bounds5 l).1) (fun l => (half_14_04_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_04_total1, half_14_04_total2, half_14_04_total3, half_14_04_total4, half_14_04_total5, half_14_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_04)
    (by simpa only [half_14_04_φ6, show (2:ℝ)*32=64 by norm_num] using half_14_04_hx6)
  exact h.weaken (by norm_num [half_14_04_total1, half_14_04_total2, half_14_04_total3, half_14_04_total4, half_14_04_total5, half_14_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_04_hx4 : SourcePowerBound
    (powerBoxCross 9 10 16 half_14_04_φ4) (19470496691/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (181868507/2500000000 : ℝ)) half_14_04_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_04_bounds4 l).1) (fun l => (half_14_04_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_04_total1, half_14_04_total2, half_14_04_total3, half_14_04_total4, half_14_04_total5, half_14_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_04)
    (by simpa only [half_14_04_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_04_hx5)
  exact h.weaken (by norm_num [half_14_04_total1, half_14_04_total2, half_14_04_total3, half_14_04_total4, half_14_04_total5, half_14_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_04_hx3 : SourcePowerBound
    (powerBoxCross 9 11 8 half_14_04_φ3) (23509437463/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (854615451/10000000000 : ℝ)) half_14_04_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_04_bounds3 l).1) (fun l => (half_14_04_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_04_total1, half_14_04_total2, half_14_04_total3, half_14_04_total4, half_14_04_total5, half_14_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_04) (half_12_04)
    (by simpa only [half_14_04_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_04_hx4)
  exact h.weaken (by norm_num [half_14_04_total1, half_14_04_total2, half_14_04_total3, half_14_04_total4, half_14_04_total5, half_14_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_04_hx2 : SourcePowerBound
    (powerBoxCross 9 12 4 half_14_04_φ2) (71224712087/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (28806317/312500000 : ℝ)) half_14_04_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_04_bounds2 l).1) (fun l => (half_14_04_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_04_total1, half_14_04_total2, half_14_04_total3, half_14_04_total4, half_14_04_total5, half_14_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_04) (half_13_04)
    (by simpa only [half_14_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_04_hx3)
  exact h.weaken (by norm_num [half_14_04_total1, half_14_04_total2, half_14_04_total3, half_14_04_total4, half_14_04_total5, half_14_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_04_hx1 : SourcePowerBound
    (powerBoxCross 9 13 2 half_14_04_φ1) (86049166329/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (1544953/16000000 : ℝ)) half_14_04_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_04_bounds1 l).1) (fun l => (half_14_04_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_04_total1, half_14_04_total2, half_14_04_total3, half_14_04_total4, half_14_04_total5, half_14_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_04) (half_14_03)
    (by simpa only [half_14_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_04_hx2)
  exact h.weaken (by norm_num [half_14_04_total1, half_14_04_total2, half_14_04_total3, half_14_04_total4, half_14_04_total5, half_14_04_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_14_04 : AdmissibleExponent 9 28 (98659856779/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 12) (ψ := (252213809/2500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_13_04)
    (by simpa only [half_14_04_φ1] using half_14_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_04_total1, half_14_04_total2, half_14_04_total3, half_14_04_total4, half_14_04_total5, half_14_04_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_15_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (514164627/5000000000 : ℝ)

private theorem half_15_04_total1 : total half_15_04_φ1=(514164627/5000000000 : ℝ) := by
  norm_num [half_15_04_φ1,total,emptyPhi,Fin.snoc]

private theorem half_15_04_bounds1 : ∀ l,0≤half_15_04_φ1 l ∧ half_15_04_φ1 l≤1 ∧
    0≤shiftExponents 9 half_15_04_φ1 l :=
  alternate_bounds_snoc emptyPhi (514164627/5000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_15_04_φ2 : Fin 2 → ℝ := Fin.snoc half_15_04_φ1 (4948043/50000000 : ℝ)

private theorem half_15_04_total2 : total half_15_04_φ2=(1008968927/5000000000 : ℝ) := by
  change total (Fin.snoc half_15_04_φ1 (4948043/50000000 : ℝ))=(1008968927/5000000000 : ℝ)
  rw [alternate_total_snoc,half_15_04_total1]
  norm_num

private theorem half_15_04_bounds2 : ∀ l,0≤half_15_04_φ2 l ∧ half_15_04_φ2 l≤1 ∧
    0≤shiftExponents 9 half_15_04_φ2 l :=
  alternate_bounds_snoc half_15_04_φ1 (4948043/50000000 : ℝ) half_15_04_bounds1 (by norm_num)

private def half_15_04_φ3 : Fin 3 → ℝ := Fin.snoc half_15_04_φ2 (475934439/5000000000 : ℝ)

private theorem half_15_04_total3 : total half_15_04_φ3=(742451683/2500000000 : ℝ) := by
  change total (Fin.snoc half_15_04_φ2 (475934439/5000000000 : ℝ))=(742451683/2500000000 : ℝ)
  rw [alternate_total_snoc,half_15_04_total2]
  norm_num

private theorem half_15_04_bounds3 : ∀ l,0≤half_15_04_φ3 l ∧ half_15_04_φ3 l≤1 ∧
    0≤shiftExponents 9 half_15_04_φ3 l :=
  alternate_bounds_snoc half_15_04_φ2 (475934439/5000000000 : ℝ) half_15_04_bounds2 (by norm_num)

private def half_15_04_φ4 : Fin 4 → ℝ := Fin.snoc half_15_04_φ3 (439387079/5000000000 : ℝ)

private theorem half_15_04_total4 : total half_15_04_φ4=(384858089/1000000000 : ℝ) := by
  change total (Fin.snoc half_15_04_φ3 (439387079/5000000000 : ℝ))=(384858089/1000000000 : ℝ)
  rw [alternate_total_snoc,half_15_04_total3]
  norm_num

private theorem half_15_04_bounds4 : ∀ l,0≤half_15_04_φ4 l ∧ half_15_04_φ4 l≤1 ∧
    0≤shiftExponents 9 half_15_04_φ4 l :=
  alternate_bounds_snoc half_15_04_φ3 (439387079/5000000000 : ℝ) half_15_04_bounds3 (by norm_num)

private def half_15_04_φ5 : Fin 5 → ℝ := Fin.snoc half_15_04_φ4 (192231847/2500000000 : ℝ)

private theorem half_15_04_total5 : total half_15_04_φ5=(2308754139/5000000000 : ℝ) := by
  change total (Fin.snoc half_15_04_φ4 (192231847/2500000000 : ℝ))=(2308754139/5000000000 : ℝ)
  rw [alternate_total_snoc,half_15_04_total4]
  norm_num

private theorem half_15_04_bounds5 : ∀ l,0≤half_15_04_φ5 l ∧ half_15_04_φ5 l≤1 ∧
    0≤shiftExponents 9 half_15_04_φ5 l :=
  alternate_bounds_snoc half_15_04_φ4 (192231847/2500000000 : ℝ) half_15_04_bounds4 (by norm_num)

private def half_15_04_φ6 : Fin 6 → ℝ := Fin.snoc half_15_04_φ5 (555819697/10000000000 : ℝ)

private theorem half_15_04_total6 : total half_15_04_φ6=(206933119/400000000 : ℝ) := by
  change total (Fin.snoc half_15_04_φ5 (555819697/10000000000 : ℝ))=(206933119/400000000 : ℝ)
  rw [alternate_total_snoc,half_15_04_total5]
  norm_num

private theorem half_15_04_bounds6 : ∀ l,0≤half_15_04_φ6 l ∧ half_15_04_φ6 l≤1 ∧
    0≤shiftExponents 9 half_15_04_φ6 l :=
  alternate_bounds_snoc half_15_04_φ5 (555819697/10000000000 : ℝ) half_15_04_bounds5 (by norm_num)

private theorem half_15_04_prefix : PrefixCondition 9 half_15_04_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_15_04_φ1, half_15_04_φ2, half_15_04_φ3, half_15_04_φ4, half_15_04_φ5, half_15_04_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_15_04_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_15_04_φ6) (379200643/50000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_15_04_φ6
    (fun i => (half_15_04_bounds6 i).1) (fun i => (half_15_04_bounds6 i).2.1)
    (fun i => (half_15_04_bounds6 i).2.2) half_15_04_prefix
  convert h using 1 <;> norm_num [half_15_04_total1, half_15_04_total2, half_15_04_total3, half_15_04_total4, half_15_04_total5, half_15_04_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_15_04_hx6 : SourcePowerBound
    (powerBoxCross 9 9 64 half_15_04_φ6) (77396958957/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 9) (r := 2) (v := 0) (w := 12) (D := 64)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_15_04_φ6 (by norm_num [half_15_04_total1, half_15_04_total2, half_15_04_total3, half_15_04_total4, half_15_04_total5, half_15_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_15_04_total1, half_15_04_total2, half_15_04_total3, half_15_04_total4, half_15_04_total5, half_15_04_total6, parameterExponent, curveLoss, dyadicExponent]) half_15_04_hF2
    (admissibleExponent_zero 9) (half_12_04)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_04_total1, half_15_04_total2, half_15_04_total3, half_15_04_total4, half_15_04_total5, half_15_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_04_hx5 : SourcePowerBound
    (powerBoxCross 9 10 32 half_15_04_φ5) (88754981367/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 10) (u := 8) (t := 11)
    (D := 32) (ψ := (555819697/10000000000 : ℝ)) half_15_04_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_04_bounds5 l).1) (fun l => (half_15_04_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_04_total1, half_15_04_total2, half_15_04_total3, half_15_04_total4, half_15_04_total5, half_15_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_04)
    (by simpa only [half_15_04_φ6, show (2:ℝ)*32=64 by norm_num] using half_15_04_hx6)
  exact h.weaken (by norm_num [half_15_04_total1, half_15_04_total2, half_15_04_total3, half_15_04_total4, half_15_04_total5, half_15_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_04_hx4 : SourcePowerBound
    (powerBoxCross 9 11 16 half_15_04_φ4) (13242309823/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (192231847/2500000000 : ℝ)) half_15_04_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_04_bounds4 l).1) (fun l => (half_15_04_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_04_total1, half_15_04_total2, half_15_04_total3, half_15_04_total4, half_15_04_total5, half_15_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_04) (half_12_04)
    (by simpa only [half_15_04_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_04_hx5)
  exact h.weaken (by norm_num [half_15_04_total1, half_15_04_total2, half_15_04_total3, half_15_04_total4, half_15_04_total5, half_15_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_04_hx3 : SourcePowerBound
    (powerBoxCross 9 12 8 half_15_04_φ3) (8018451631/625000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (439387079/5000000000 : ℝ)) half_15_04_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_04_bounds3 l).1) (fun l => (half_15_04_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_04_total1, half_15_04_total2, half_15_04_total3, half_15_04_total4, half_15_04_total5, half_15_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_04) (half_13_04)
    (by simpa only [half_15_04_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_04_hx4)
  exact h.weaken (by norm_num [half_15_04_total1, half_15_04_total2, half_15_04_total3, half_15_04_total4, half_15_04_total5, half_15_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_04_hx2 : SourcePowerBound
    (powerBoxCross 9 13 4 half_15_04_φ2) (77886632271/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (475934439/5000000000 : ℝ)) half_15_04_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_04_bounds2 l).1) (fun l => (half_15_04_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_04_total1, half_15_04_total2, half_15_04_total3, half_15_04_total4, half_15_04_total5, half_15_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_04) (half_14_04)
    (by simpa only [half_15_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_04_hx3)
  exact h.weaken (by norm_num [half_15_04_total1, half_15_04_total2, half_15_04_total3, half_15_04_total4, half_15_04_total5, half_15_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_04_hx1 : SourcePowerBound
    (powerBoxCross 9 14 2 half_15_04_φ1) (188057079431/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (4948043/50000000 : ℝ)) half_15_04_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_04_bounds1 l).1) (fun l => (half_15_04_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_04_total1, half_15_04_total2, half_15_04_total3, half_15_04_total4, half_15_04_total5, half_15_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_04) (half_15_03)
    (by simpa only [half_15_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_04_hx2)
  exact h.weaken (by norm_num [half_15_04_total1, half_15_04_total2, half_15_04_total3, half_15_04_total4, half_15_04_total5, half_15_04_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_15_04 : AdmissibleExponent 9 30 (215821969289/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 13) (ψ := (514164627/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_14_04)
    (by simpa only [half_15_04_φ1] using half_15_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_04_total1, half_15_04_total2, half_15_04_total3, half_15_04_total4, half_15_04_total5, half_15_04_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_16_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1046367883/10000000000 : ℝ)

private theorem half_16_04_total1 : total half_16_04_φ1=(1046367883/10000000000 : ℝ) := by
  norm_num [half_16_04_φ1,total,emptyPhi,Fin.snoc]

private theorem half_16_04_bounds1 : ∀ l,0≤half_16_04_φ1 l ∧ half_16_04_φ1 l≤1 ∧
    0≤shiftExponents 9 half_16_04_φ1 l :=
  alternate_bounds_snoc emptyPhi (1046367883/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_16_04_φ2 : Fin 2 → ℝ := Fin.snoc half_16_04_φ1 (506107761/5000000000 : ℝ)

private theorem half_16_04_total2 : total half_16_04_φ2=(411716681/2000000000 : ℝ) := by
  change total (Fin.snoc half_16_04_φ1 (506107761/5000000000 : ℝ))=(411716681/2000000000 : ℝ)
  rw [alternate_total_snoc,half_16_04_total1]
  norm_num

private theorem half_16_04_bounds2 : ∀ l,0≤half_16_04_φ2 l ∧ half_16_04_φ2 l≤1 ∧
    0≤shiftExponents 9 half_16_04_φ2 l :=
  alternate_bounds_snoc half_16_04_φ1 (506107761/5000000000 : ℝ) half_16_04_bounds1 (by norm_num)

private def half_16_04_φ3 : Fin 3 → ℝ := Fin.snoc half_16_04_φ2 (245690799/2500000000 : ℝ)

private theorem half_16_04_total3 : total half_16_04_φ3=(3041346601/10000000000 : ℝ) := by
  change total (Fin.snoc half_16_04_φ2 (245690799/2500000000 : ℝ))=(3041346601/10000000000 : ℝ)
  rw [alternate_total_snoc,half_16_04_total2]
  norm_num

private theorem half_16_04_bounds3 : ∀ l,0≤half_16_04_φ3 l ∧ half_16_04_φ3 l≤1 ∧
    0≤shiftExponents 9 half_16_04_φ3 l :=
  alternate_bounds_snoc half_16_04_φ2 (245690799/2500000000 : ℝ) half_16_04_bounds2 (by norm_num)

private def half_16_04_φ4 : Fin 4 → ℝ := Fin.snoc half_16_04_φ3 (434915837/5000000000 : ℝ)

private theorem half_16_04_total4 : total half_16_04_φ4=(156447131/400000000 : ℝ) := by
  change total (Fin.snoc half_16_04_φ3 (434915837/5000000000 : ℝ))=(156447131/400000000 : ℝ)
  rw [alternate_total_snoc,half_16_04_total3]
  norm_num

private theorem half_16_04_bounds4 : ∀ l,0≤half_16_04_φ4 l ∧ half_16_04_φ4 l≤1 ∧
    0≤shiftExponents 9 half_16_04_φ4 l :=
  alternate_bounds_snoc half_16_04_φ3 (434915837/5000000000 : ℝ) half_16_04_bounds3 (by norm_num)

private def half_16_04_φ5 : Fin 5 → ℝ := Fin.snoc half_16_04_φ4 (152220543/2000000000 : ℝ)

private theorem half_16_04_total5 : total half_16_04_φ5=(467228099/1000000000 : ℝ) := by
  change total (Fin.snoc half_16_04_φ4 (152220543/2000000000 : ℝ))=(467228099/1000000000 : ℝ)
  rw [alternate_total_snoc,half_16_04_total4]
  norm_num

private theorem half_16_04_bounds5 : ∀ l,0≤half_16_04_φ5 l ∧ half_16_04_φ5 l≤1 ∧
    0≤shiftExponents 9 half_16_04_φ5 l :=
  alternate_bounds_snoc half_16_04_φ4 (152220543/2000000000 : ℝ) half_16_04_bounds4 (by norm_num)

private def half_16_04_φ6 : Fin 6 → ℝ := Fin.snoc half_16_04_φ5 (166491219/2500000000 : ℝ)

private theorem half_16_04_total6 : total half_16_04_φ6=(2669122933/5000000000 : ℝ) := by
  change total (Fin.snoc half_16_04_φ5 (166491219/2500000000 : ℝ))=(2669122933/5000000000 : ℝ)
  rw [alternate_total_snoc,half_16_04_total5]
  norm_num

private theorem half_16_04_bounds6 : ∀ l,0≤half_16_04_φ6 l ∧ half_16_04_φ6 l≤1 ∧
    0≤shiftExponents 9 half_16_04_φ6 l :=
  alternate_bounds_snoc half_16_04_φ5 (166491219/2500000000 : ℝ) half_16_04_bounds5 (by norm_num)

private theorem half_16_04_prefix : PrefixCondition 9 half_16_04_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_16_04_φ1, half_16_04_φ2, half_16_04_φ3, half_16_04_φ4, half_16_04_φ5, half_16_04_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_16_04_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_16_04_φ6) (4492631201/625000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_16_04_φ6
    (fun i => (half_16_04_bounds6 i).1) (fun i => (half_16_04_bounds6 i).2.1)
    (fun i => (half_16_04_bounds6 i).2.2) half_16_04_prefix
  convert h using 1 <;> norm_num [half_16_04_total1, half_16_04_total2, half_16_04_total3, half_16_04_total4, half_16_04_total5, half_16_04_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_16_04_hx6 : SourcePowerBound
    (powerBoxCross 9 10 64 half_16_04_φ6) (413639941/50000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 10) (r := 2) (v := 13) (w := 14) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_16_04_φ6 (by norm_num [half_16_04_total1, half_16_04_total2, half_16_04_total3, half_16_04_total4, half_16_04_total5, half_16_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_16_04_total1, half_16_04_total2, half_16_04_total3, half_16_04_total4, half_16_04_total5, half_16_04_total6, parameterExponent, curveLoss, dyadicExponent]) half_16_04_hF2
    (half_13_04) (half_14_04)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_04_total1, half_16_04_total2, half_16_04_total3, half_16_04_total4, half_16_04_total5, half_16_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_04_hx5 : SourcePowerBound
    (powerBoxCross 9 11 32 half_16_04_φ5) (12125454147/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 11) (u := 9) (t := 12)
    (D := 32) (ψ := (166491219/2500000000 : ℝ)) half_16_04_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_04_bounds5 l).1) (fun l => (half_16_04_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_04_total1, half_16_04_total2, half_16_04_total3, half_16_04_total4, half_16_04_total5, half_16_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_04) (half_12_04)
    (by simpa only [half_16_04_φ6, show (2:ℝ)*32=64 by norm_num] using half_16_04_hx6)
  exact h.weaken (by norm_num [half_16_04_total1, half_16_04_total2, half_16_04_total3, half_16_04_total4, half_16_04_total5, half_16_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_04_hx4 : SourcePowerBound
    (powerBoxCross 9 12 16 half_16_04_φ4) (23078748939/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (152220543/2000000000 : ℝ)) half_16_04_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_04_bounds4 l).1) (fun l => (half_16_04_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_04_total1, half_16_04_total2, half_16_04_total3, half_16_04_total4, half_16_04_total5, half_16_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_04) (half_13_04)
    (by simpa only [half_16_04_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_04_hx5)
  exact h.weaken (by norm_num [half_16_04_total1, half_16_04_total2, half_16_04_total3, half_16_04_total4, half_16_04_total5, half_16_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_04_hx3 : SourcePowerBound
    (powerBoxCross 9 13 8 half_16_04_φ3) (139188524967/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (434915837/5000000000 : ℝ)) half_16_04_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_04_bounds3 l).1) (fun l => (half_16_04_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_04_total1, half_16_04_total2, half_16_04_total3, half_16_04_total4, half_16_04_total5, half_16_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_04) (half_14_04)
    (by simpa only [half_16_04_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_04_hx4)
  exact h.weaken (by norm_num [half_16_04_total1, half_16_04_total2, half_16_04_total3, half_16_04_total4, half_16_04_total5, half_16_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_04_hx2 : SourcePowerBound
    (powerBoxCross 9 14 4 half_16_04_φ2) (84670538619/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (245690799/2500000000 : ℝ)) half_16_04_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_04_bounds2 l).1) (fun l => (half_16_04_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_04_total1, half_16_04_total2, half_16_04_total3, half_16_04_total4, half_16_04_total5, half_16_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_04) (half_15_04)
    (by simpa only [half_16_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_04_hx3)
  exact h.weaken (by norm_num [half_16_04_total1, half_16_04_total2, half_16_04_total3, half_16_04_total4, half_16_04_total5, half_16_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_04_hx1 : SourcePowerBound
    (powerBoxCross 9 15 2 half_16_04_φ1) (40857083893/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (506107761/5000000000 : ℝ)) half_16_04_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_04_bounds1 l).1) (fun l => (half_16_04_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_04_total1, half_16_04_total2, half_16_04_total3, half_16_04_total4, half_16_04_total5, half_16_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_04) (half_16_03)
    (by simpa only [half_16_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_04_hx2)
  exact h.weaken (by norm_num [half_16_04_total1, half_16_04_total2, half_16_04_total3, half_16_04_total4, half_16_04_total5, half_16_04_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_16_04 : AdmissibleExponent 9 32 (29328761009/1250000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 14) (ψ := (1046367883/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_15_04)
    (by simpa only [half_16_04_φ1] using half_16_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_04_total1, half_16_04_total2, half_16_04_total3, half_16_04_total4, half_16_04_total5, half_16_04_total6, parameterExponent, curveLoss, dyadicExponent])

theorem chord_70 : AdmissibleExponent 9 34 (507775125123/20000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 34) (t := (1/2 : ℝ))
    (half_16_04) (half_18_03)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_17_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (530590913/5000000000 : ℝ)

private theorem half_17_04_total1 : total half_17_04_φ1=(530590913/5000000000 : ℝ) := by
  norm_num [half_17_04_φ1,total,emptyPhi,Fin.snoc]

private theorem half_17_04_bounds1 : ∀ l,0≤half_17_04_φ1 l ∧ half_17_04_φ1 l≤1 ∧
    0≤shiftExponents 9 half_17_04_φ1 l :=
  alternate_bounds_snoc emptyPhi (530590913/5000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_17_04_φ2 : Fin 2 → ℝ := Fin.snoc half_17_04_φ1 (1033476539/10000000000 : ℝ)

private theorem half_17_04_total2 : total half_17_04_φ2=(418931673/2000000000 : ℝ) := by
  change total (Fin.snoc half_17_04_φ1 (1033476539/10000000000 : ℝ))=(418931673/2000000000 : ℝ)
  rw [alternate_total_snoc,half_17_04_total1]
  norm_num

private theorem half_17_04_bounds2 : ∀ l,0≤half_17_04_φ2 l ∧ half_17_04_φ2 l≤1 ∧
    0≤shiftExponents 9 half_17_04_φ2 l :=
  alternate_bounds_snoc half_17_04_φ1 (1033476539/10000000000 : ℝ) half_17_04_bounds1 (by norm_num)

private def half_17_04_φ3 : Fin 3 → ℝ := Fin.snoc half_17_04_φ2 (123520963/1250000000 : ℝ)

private theorem half_17_04_total3 : total half_17_04_φ3=(3082826069/10000000000 : ℝ) := by
  change total (Fin.snoc half_17_04_φ2 (123520963/1250000000 : ℝ))=(3082826069/10000000000 : ℝ)
  rw [alternate_total_snoc,half_17_04_total2]
  norm_num

private theorem half_17_04_bounds3 : ∀ l,0≤half_17_04_φ3 l ∧ half_17_04_φ3 l≤1 ∧
    0≤shiftExponents 9 half_17_04_φ3 l :=
  alternate_bounds_snoc half_17_04_φ2 (123520963/1250000000 : ℝ) half_17_04_bounds2 (by norm_num)

private def half_17_04_φ4 : Fin 4 → ℝ := Fin.snoc half_17_04_φ3 (864646741/10000000000 : ℝ)

private theorem half_17_04_total4 : total half_17_04_φ4=(394747281/1000000000 : ℝ) := by
  change total (Fin.snoc half_17_04_φ3 (864646741/10000000000 : ℝ))=(394747281/1000000000 : ℝ)
  rw [alternate_total_snoc,half_17_04_total3]
  norm_num

private theorem half_17_04_bounds4 : ∀ l,0≤half_17_04_φ4 l ∧ half_17_04_φ4 l≤1 ∧
    0≤shiftExponents 9 half_17_04_φ4 l :=
  alternate_bounds_snoc half_17_04_φ3 (864646741/10000000000 : ℝ) half_17_04_bounds3 (by norm_num)

private def half_17_04_φ5 : Fin 5 → ℝ := Fin.snoc half_17_04_φ4 (378282949/5000000000 : ℝ)

private theorem half_17_04_total5 : total half_17_04_φ5=(1176009677/2500000000 : ℝ) := by
  change total (Fin.snoc half_17_04_φ4 (378282949/5000000000 : ℝ))=(1176009677/2500000000 : ℝ)
  rw [alternate_total_snoc,half_17_04_total4]
  norm_num

private theorem half_17_04_bounds5 : ∀ l,0≤half_17_04_φ5 l ∧ half_17_04_φ5 l≤1 ∧
    0≤shiftExponents 9 half_17_04_φ5 l :=
  alternate_bounds_snoc half_17_04_φ4 (378282949/5000000000 : ℝ) half_17_04_bounds4 (by norm_num)

private def half_17_04_φ6 : Fin 6 → ℝ := Fin.snoc half_17_04_φ5 (661995161/10000000000 : ℝ)

private theorem half_17_04_total6 : total half_17_04_φ6=(5366033869/10000000000 : ℝ) := by
  change total (Fin.snoc half_17_04_φ5 (661995161/10000000000 : ℝ))=(5366033869/10000000000 : ℝ)
  rw [alternate_total_snoc,half_17_04_total5]
  norm_num

private theorem half_17_04_bounds6 : ∀ l,0≤half_17_04_φ6 l ∧ half_17_04_φ6 l≤1 ∧
    0≤shiftExponents 9 half_17_04_φ6 l :=
  alternate_bounds_snoc half_17_04_φ5 (661995161/10000000000 : ℝ) half_17_04_bounds5 (by norm_num)

private theorem half_17_04_prefix : PrefixCondition 9 half_17_04_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_17_04_φ1, half_17_04_φ2, half_17_04_φ3, half_17_04_φ4, half_17_04_φ5, half_17_04_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_17_04_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_17_04_φ6) (8901898393/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_17_04_φ6
    (fun i => (half_17_04_bounds6 i).1) (fun i => (half_17_04_bounds6 i).2.1)
    (fun i => (half_17_04_bounds6 i).2.2) half_17_04_prefix
  convert h using 1 <;> norm_num [half_17_04_total1, half_17_04_total2, half_17_04_total3, half_17_04_total4, half_17_04_total5, half_17_04_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_17_04_hx6 : SourcePowerBound
    (powerBoxCross 9 11 64 half_17_04_φ6) (90668703327/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 11) (r := 2) (v := 14) (w := 15) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_17_04_φ6 (by norm_num [half_17_04_total1, half_17_04_total2, half_17_04_total3, half_17_04_total4, half_17_04_total5, half_17_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_17_04_total1, half_17_04_total2, half_17_04_total3, half_17_04_total4, half_17_04_total5, half_17_04_total6, parameterExponent, curveLoss, dyadicExponent]) half_17_04_hF2
    (half_14_04) (half_15_04)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_04_total1, half_17_04_total2, half_17_04_total3, half_17_04_total4, half_17_04_total5, half_17_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_04_hx5 : SourcePowerBound
    (powerBoxCross 9 12 32 half_17_04_φ5) (52955791481/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 12) (u := 10) (t := 13)
    (D := 32) (ψ := (661995161/10000000000 : ℝ)) half_17_04_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_04_bounds5 l).1) (fun l => (half_17_04_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_04_total1, half_17_04_total2, half_17_04_total3, half_17_04_total4, half_17_04_total5, half_17_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_04) (half_13_04)
    (by simpa only [half_17_04_φ6, show (2:ℝ)*32=64 by norm_num] using half_17_04_hx6)
  exact h.weaken (by norm_num [half_17_04_total1, half_17_04_total2, half_17_04_total3, half_17_04_total4, half_17_04_total5, half_17_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_04_hx4 : SourcePowerBound
    (powerBoxCross 9 13 16 half_17_04_φ4) (1569756933/125000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (378282949/5000000000 : ℝ)) half_17_04_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_04_bounds4 l).1) (fun l => (half_17_04_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_04_total1, half_17_04_total2, half_17_04_total3, half_17_04_total4, half_17_04_total5, half_17_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_04) (half_14_04)
    (by simpa only [half_17_04_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_04_hx5)
  exact h.weaken (by norm_num [half_17_04_total1, half_17_04_total2, half_17_04_total3, half_17_04_total4, half_17_04_total5, half_17_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_04_hx3 : SourcePowerBound
    (powerBoxCross 9 14 8 half_17_04_φ3) (37727740573/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (864646741/10000000000 : ℝ)) half_17_04_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_04_bounds3 l).1) (fun l => (half_17_04_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_04_total1, half_17_04_total2, half_17_04_total3, half_17_04_total4, half_17_04_total5, half_17_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_04) (half_15_04)
    (by simpa only [half_17_04_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_04_hx4)
  exact h.weaken (by norm_num [half_17_04_total1, half_17_04_total2, half_17_04_total3, half_17_04_total4, half_17_04_total5, half_17_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_04_hx2 : SourcePowerBound
    (powerBoxCross 9 15 4 half_17_04_φ2) (183158661893/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (123520963/1250000000 : ℝ)) half_17_04_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_04_bounds2 l).1) (fun l => (half_17_04_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_04_total1, half_17_04_total2, half_17_04_total3, half_17_04_total4, half_17_04_total5, half_17_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_04) (half_16_04)
    (by simpa only [half_17_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_04_hx3)
  exact h.weaken (by norm_num [half_17_04_total1, half_17_04_total2, half_17_04_total3, half_17_04_total4, half_17_04_total5, half_17_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_04_hx1 : SourcePowerBound
    (powerBoxCross 9 16 2 half_17_04_φ1) (220792751377/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (1033476539/10000000000 : ℝ)) half_17_04_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_04_bounds1 l).1) (fun l => (half_17_04_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_04_total1, half_17_04_total2, half_17_04_total3, half_17_04_total4, half_17_04_total5, half_17_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_04) (chord_70)
    (by simpa only [half_17_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_04_hx2)
  exact h.weaken (by norm_num [half_17_04_total1, half_17_04_total2, half_17_04_total3, half_17_04_total4, half_17_04_total5, half_17_04_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_17_04 : AdmissibleExponent 9 34 (253689387983/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 15) (ψ := (530590913/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_16_04)
    (by simpa only [half_17_04_φ1] using half_17_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_04_total1, half_17_04_total2, half_17_04_total3, half_17_04_total4, half_17_04_total5, half_17_04_total6, parameterExponent, curveLoss, dyadicExponent])

theorem chord_71 : AdmissibleExponent 9 36 (109251358647/4000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 36) (t := (1/2 : ℝ))
    (half_17_04) (half_19_03)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_18_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (536359191/5000000000 : ℝ)

private theorem half_18_04_total1 : total half_18_04_φ1=(536359191/5000000000 : ℝ) := by
  norm_num [half_18_04_φ1,total,emptyPhi,Fin.snoc]

private theorem half_18_04_bounds1 : ∀ l,0≤half_18_04_φ1 l ∧ half_18_04_φ1 l≤1 ∧
    0≤shiftExponents 9 half_18_04_φ1 l :=
  alternate_bounds_snoc emptyPhi (536359191/5000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_18_04_φ2 : Fin 2 → ℝ := Fin.snoc half_18_04_φ1 (1050716113/10000000000 : ℝ)

private theorem half_18_04_total2 : total half_18_04_φ2=(424686899/2000000000 : ℝ) := by
  change total (Fin.snoc half_18_04_φ1 (1050716113/10000000000 : ℝ))=(424686899/2000000000 : ℝ)
  rw [alternate_total_snoc,half_18_04_total1]
  norm_num

private theorem half_18_04_bounds2 : ∀ l,0≤half_18_04_φ2 l ∧ half_18_04_φ2 l≤1 ∧
    0≤shiftExponents 9 half_18_04_φ2 l :=
  alternate_bounds_snoc half_18_04_φ1 (1050716113/10000000000 : ℝ) half_18_04_bounds1 (by norm_num)

private def half_18_04_φ3 : Fin 3 → ℝ := Fin.snoc half_18_04_φ2 (15383917/156250000 : ℝ)

private theorem half_18_04_total3 : total half_18_04_φ3=(3108005183/10000000000 : ℝ) := by
  change total (Fin.snoc half_18_04_φ2 (15383917/156250000 : ℝ))=(3108005183/10000000000 : ℝ)
  rw [alternate_total_snoc,half_18_04_total2]
  norm_num

private theorem half_18_04_bounds3 : ∀ l,0≤half_18_04_φ3 l ∧ half_18_04_φ3 l≤1 ∧
    0≤shiftExponents 9 half_18_04_φ3 l :=
  alternate_bounds_snoc half_18_04_φ2 (15383917/156250000 : ℝ) half_18_04_bounds2 (by norm_num)

private def half_18_04_φ4 : Fin 4 → ℝ := Fin.snoc half_18_04_φ3 (107687419/1250000000 : ℝ)

private theorem half_18_04_total4 : total half_18_04_φ4=(793900907/2000000000 : ℝ) := by
  change total (Fin.snoc half_18_04_φ3 (107687419/1250000000 : ℝ))=(793900907/2000000000 : ℝ)
  rw [alternate_total_snoc,half_18_04_total3]
  norm_num

private theorem half_18_04_bounds4 : ∀ l,0≤half_18_04_φ4 l ∧ half_18_04_φ4 l≤1 ∧
    0≤shiftExponents 9 half_18_04_φ4 l :=
  alternate_bounds_snoc half_18_04_φ3 (107687419/1250000000 : ℝ) half_18_04_bounds3 (by norm_num)

private def half_18_04_φ5 : Fin 5 → ℝ := Fin.snoc half_18_04_φ4 (753811933/10000000000 : ℝ)

private theorem half_18_04_total5 : total half_18_04_φ5=(1180829117/2500000000 : ℝ) := by
  change total (Fin.snoc half_18_04_φ4 (753811933/10000000000 : ℝ))=(1180829117/2500000000 : ℝ)
  rw [alternate_total_snoc,half_18_04_total4]
  norm_num

private theorem half_18_04_bounds5 : ∀ l,0≤half_18_04_φ5 l ∧ half_18_04_φ5 l≤1 ∧
    0≤shiftExponents 9 half_18_04_φ5 l :=
  alternate_bounds_snoc half_18_04_φ4 (753811933/10000000000 : ℝ) half_18_04_bounds4 (by norm_num)

private def half_18_04_φ6 : Fin 6 → ℝ := Fin.snoc half_18_04_φ5 (659585441/10000000000 : ℝ)

private theorem half_18_04_total6 : total half_18_04_φ6=(5382901909/10000000000 : ℝ) := by
  change total (Fin.snoc half_18_04_φ5 (659585441/10000000000 : ℝ))=(5382901909/10000000000 : ℝ)
  rw [alternate_total_snoc,half_18_04_total5]
  norm_num

private theorem half_18_04_bounds6 : ∀ l,0≤half_18_04_φ6 l ∧ half_18_04_φ6 l≤1 ∧
    0≤shiftExponents 9 half_18_04_φ6 l :=
  alternate_bounds_snoc half_18_04_φ5 (659585441/10000000000 : ℝ) half_18_04_bounds5 (by norm_num)

private theorem half_18_04_prefix : PrefixCondition 9 half_18_04_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_18_04_φ1, half_18_04_φ2, half_18_04_φ3, half_18_04_φ4, half_18_04_φ5, half_18_04_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_18_04_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_18_04_φ6) (8851294273/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_18_04_φ6
    (fun i => (half_18_04_bounds6 i).1) (fun i => (half_18_04_bounds6 i).2.1)
    (fun i => (half_18_04_bounds6 i).2.2) half_18_04_prefix
  convert h using 1 <;> norm_num [half_18_04_total1, half_18_04_total2, half_18_04_total3, half_18_04_total4, half_18_04_total5, half_18_04_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_18_04_hx6 : SourcePowerBound
    (powerBoxCross 9 12 64 half_18_04_φ6) (49475424213/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 12) (r := 2) (v := 0) (w := 16) (D := 64)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_18_04_φ6 (by norm_num [half_18_04_total1, half_18_04_total2, half_18_04_total3, half_18_04_total4, half_18_04_total5, half_18_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_18_04_total1, half_18_04_total2, half_18_04_total3, half_18_04_total4, half_18_04_total5, half_18_04_total6, parameterExponent, curveLoss, dyadicExponent]) half_18_04_hF2
    (admissibleExponent_zero 9) (half_16_04)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_18_04_total1, half_18_04_total2, half_18_04_total3, half_18_04_total4, half_18_04_total5, half_18_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_04_hx5 : SourcePowerBound
    (powerBoxCross 9 13 32 half_18_04_φ5) (115227075067/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 13) (u := 11) (t := 14)
    (D := 32) (ψ := (659585441/10000000000 : ℝ)) half_18_04_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_04_bounds5 l).1) (fun l => (half_18_04_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_04_total1, half_18_04_total2, half_18_04_total3, half_18_04_total4, half_18_04_total5, half_18_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_04) (half_14_04)
    (by simpa only [half_18_04_φ6, show (2:ℝ)*32=64 by norm_num] using half_18_04_hx6)
  exact h.weaken (by norm_num [half_18_04_total1, half_18_04_total2, half_18_04_total3, half_18_04_total4, half_18_04_total5, half_18_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_04_hx4 : SourcePowerBound
    (powerBoxCross 9 14 16 half_18_04_φ4) (136233838909/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 14) (u := 12) (t := 15)
    (D := 16) (ψ := (753811933/10000000000 : ℝ)) half_18_04_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_04_bounds4 l).1) (fun l => (half_18_04_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_04_total1, half_18_04_total2, half_18_04_total3, half_18_04_total4, half_18_04_total5, half_18_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_04) (half_15_04)
    (by simpa only [half_18_04_φ5, show (2:ℝ)*16=32 by norm_num] using half_18_04_hx5)
  exact h.weaken (by norm_num [half_18_04_total1, half_18_04_total2, half_18_04_total3, half_18_04_total4, half_18_04_total5, half_18_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_04_hx3 : SourcePowerBound
    (powerBoxCross 9 15 8 half_18_04_φ3) (1019803797/62500000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 15) (u := 13) (t := 16)
    (D := 8) (ψ := (107687419/1250000000 : ℝ)) half_18_04_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_04_bounds3 l).1) (fun l => (half_18_04_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_04_total1, half_18_04_total2, half_18_04_total3, half_18_04_total4, half_18_04_total5, half_18_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_04) (half_16_04)
    (by simpa only [half_18_04_φ4, show (2:ℝ)*8=16 by norm_num] using half_18_04_hx4)
  exact h.weaken (by norm_num [half_18_04_total1, half_18_04_total2, half_18_04_total3, half_18_04_total4, half_18_04_total5, half_18_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_04_hx2 : SourcePowerBound
    (powerBoxCross 9 16 4 half_18_04_φ2) (1578215159/80000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 16) (u := 14) (t := 17)
    (D := 4) (ψ := (15383917/156250000 : ℝ)) half_18_04_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_04_bounds2 l).1) (fun l => (half_18_04_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_04_total1, half_18_04_total2, half_18_04_total3, half_18_04_total4, half_18_04_total5, half_18_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_04) (half_17_04)
    (by simpa only [half_18_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_18_04_hx3)
  exact h.weaken (by norm_num [half_18_04_total1, half_18_04_total2, half_18_04_total3, half_18_04_total4, half_18_04_total5, half_18_04_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_04_hx1 : SourcePowerBound
    (powerBoxCross 9 17 2 half_18_04_φ1) (47509675877/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 17) (u := 15) (t := 18)
    (D := 2) (ψ := (1050716113/10000000000 : ℝ)) half_18_04_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_04_bounds1 l).1) (fun l => (half_18_04_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_04_total1, half_18_04_total2, half_18_04_total3, half_18_04_total4, half_18_04_total5, half_18_04_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_04) (chord_71)
    (by simpa only [half_18_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_18_04_hx2)
  exact h.weaken (by norm_num [half_18_04_total1, half_18_04_total2, half_18_04_total3, half_18_04_total4, half_18_04_total5, half_18_04_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_18_04 : AdmissibleExponent 9 36 (272948085991/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 16) (ψ := (536359191/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_17_04)
    (by simpa only [half_18_04_φ1] using half_18_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_18_04_total1, half_18_04_total2, half_18_04_total3, half_18_04_total4, half_18_04_total5, half_18_04_total6, parameterExponent, curveLoss, dyadicExponent])

theorem chord_72 : AdmissibleExponent 9 38 (292543823953/10000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 38) (t := (1/2 : ℝ))
    (half_18_04) (half_20_03)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

end Waring.SeedCompletionAlternate9Seeds
