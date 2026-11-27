import Waring.SeedCompletionAlternate9Steps06

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionAlternate9Seeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges SeedCompletionDivisorPowerScales
open PolicyCompletionSharpResidualSource

private def half_17_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (105858643/1000000000 : ℝ)

private theorem half_17_06_total1 : total half_17_06_φ1=(105858643/1000000000 : ℝ) := by
  norm_num [half_17_06_φ1,total,emptyPhi,Fin.snoc]

private theorem half_17_06_bounds1 : ∀ l,0≤half_17_06_φ1 l ∧ half_17_06_φ1 l≤1 ∧
    0≤shiftExponents 9 half_17_06_φ1 l :=
  alternate_bounds_snoc emptyPhi (105858643/1000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_17_06_φ2 : Fin 2 → ℝ := Fin.snoc half_17_06_φ1 (1035655147/10000000000 : ℝ)

private theorem half_17_06_total2 : total half_17_06_φ2=(2094241577/10000000000 : ℝ) := by
  change total (Fin.snoc half_17_06_φ1 (1035655147/10000000000 : ℝ))=(2094241577/10000000000 : ℝ)
  rw [alternate_total_snoc,half_17_06_total1]
  norm_num

private theorem half_17_06_bounds2 : ∀ l,0≤half_17_06_φ2 l ∧ half_17_06_φ2 l≤1 ∧
    0≤shiftExponents 9 half_17_06_φ2 l :=
  alternate_bounds_snoc half_17_06_φ1 (1035655147/10000000000 : ℝ) half_17_06_bounds1 (by norm_num)

private def half_17_06_φ3 : Fin 3 → ℝ := Fin.snoc half_17_06_φ2 (494109901/5000000000 : ℝ)

private theorem half_17_06_total3 : total half_17_06_φ3=(3082461379/10000000000 : ℝ) := by
  change total (Fin.snoc half_17_06_φ2 (494109901/5000000000 : ℝ))=(3082461379/10000000000 : ℝ)
  rw [alternate_total_snoc,half_17_06_total2]
  norm_num

private theorem half_17_06_bounds3 : ∀ l,0≤half_17_06_φ3 l ∧ half_17_06_φ3 l≤1 ∧
    0≤shiftExponents 9 half_17_06_φ3 l :=
  alternate_bounds_snoc half_17_06_φ2 (494109901/5000000000 : ℝ) half_17_06_bounds2 (by norm_num)

private def half_17_06_φ4 : Fin 4 → ℝ := Fin.snoc half_17_06_φ3 (864692327/10000000000 : ℝ)

private theorem half_17_06_total4 : total half_17_06_φ4=(1973576853/5000000000 : ℝ) := by
  change total (Fin.snoc half_17_06_φ3 (864692327/10000000000 : ℝ))=(1973576853/5000000000 : ℝ)
  rw [alternate_total_snoc,half_17_06_total3]
  norm_num

private theorem half_17_06_bounds4 : ∀ l,0≤half_17_06_φ4 l ∧ half_17_06_φ4 l≤1 ∧
    0≤shiftExponents 9 half_17_06_φ4 l :=
  alternate_bounds_snoc half_17_06_φ3 (864692327/10000000000 : ℝ) half_17_06_bounds3 (by norm_num)

private def half_17_06_φ5 : Fin 5 → ℝ := Fin.snoc half_17_06_φ4 (378302893/5000000000 : ℝ)

private theorem half_17_06_total5 : total half_17_06_φ5=(1175939873/2500000000 : ℝ) := by
  change total (Fin.snoc half_17_06_φ4 (378302893/5000000000 : ℝ))=(1175939873/2500000000 : ℝ)
  rw [alternate_total_snoc,half_17_06_total4]
  norm_num

private theorem half_17_06_bounds5 : ∀ l,0≤half_17_06_φ5 l ∧ half_17_06_φ5 l≤1 ∧
    0≤shiftExponents 9 half_17_06_φ5 l :=
  alternate_bounds_snoc half_17_06_φ4 (378302893/5000000000 : ℝ) half_17_06_bounds4 (by norm_num)

private def half_17_06_φ6 : Fin 6 → ℝ := Fin.snoc half_17_06_φ5 (662030063/10000000000 : ℝ)

private theorem half_17_06_total6 : total half_17_06_φ6=(1073157911/2000000000 : ℝ) := by
  change total (Fin.snoc half_17_06_φ5 (662030063/10000000000 : ℝ))=(1073157911/2000000000 : ℝ)
  rw [alternate_total_snoc,half_17_06_total5]
  norm_num

private theorem half_17_06_bounds6 : ∀ l,0≤half_17_06_φ6 l ∧ half_17_06_φ6 l≤1 ∧
    0≤shiftExponents 9 half_17_06_φ6 l :=
  alternate_bounds_snoc half_17_06_φ5 (662030063/10000000000 : ℝ) half_17_06_bounds5 (by norm_num)

private theorem half_17_06_prefix : PrefixCondition 9 half_17_06_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_17_06_φ1, half_17_06_φ2, half_17_06_φ3, half_17_06_φ4, half_17_06_φ5, half_17_06_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_17_06_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_17_06_φ6) (1780526267/250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_17_06_φ6
    (fun i => (half_17_06_bounds6 i).1) (fun i => (half_17_06_bounds6 i).2.1)
    (fun i => (half_17_06_bounds6 i).2.2) half_17_06_prefix
  convert h using 1 <;> norm_num [half_17_06_total1, half_17_06_total2, half_17_06_total3, half_17_06_total4, half_17_06_total5, half_17_06_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_17_06_hx6 : SourcePowerBound
    (powerBoxCross 9 11 64 half_17_06_φ6) (3624073893/400000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 11) (r := 2) (v := 14) (w := 15) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_17_06_φ6 (by norm_num [half_17_06_total1, half_17_06_total2, half_17_06_total3, half_17_06_total4, half_17_06_total5, half_17_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_17_06_total1, half_17_06_total2, half_17_06_total3, half_17_06_total4, half_17_06_total5, half_17_06_total6, parameterExponent, curveLoss, dyadicExponent]) half_17_06_hF2
    (half_14_06) (half_15_06)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_06_total1, half_17_06_total2, half_17_06_total3, half_17_06_total4, half_17_06_total5, half_17_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_06_hx5 : SourcePowerBound
    (powerBoxCross 9 12 32 half_17_06_φ5) (13230074687/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 12) (u := 10) (t := 13)
    (D := 32) (ψ := (662030063/10000000000 : ℝ)) half_17_06_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_06_bounds5 l).1) (fun l => (half_17_06_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_06_total1, half_17_06_total2, half_17_06_total3, half_17_06_total4, half_17_06_total5, half_17_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_06) (half_13_06)
    (by simpa only [half_17_06_φ6, show (2:ℝ)*32=64 by norm_num] using half_17_06_hx6)
  exact h.weaken (by norm_num [half_17_06_total1, half_17_06_total2, half_17_06_total3, half_17_06_total4, half_17_06_total5, half_17_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_06_hx4 : SourcePowerBound
    (powerBoxCross 9 13 16 half_17_06_φ4) (62745923107/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (378302893/5000000000 : ℝ)) half_17_06_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_06_bounds4 l).1) (fun l => (half_17_06_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_06_total1, half_17_06_total2, half_17_06_total3, half_17_06_total4, half_17_06_total5, half_17_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_06) (half_14_06)
    (by simpa only [half_17_06_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_06_hx5)
  exact h.weaken (by norm_num [half_17_06_total1, half_17_06_total2, half_17_06_total3, half_17_06_total4, half_17_06_total5, half_17_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_06_hx3 : SourcePowerBound
    (powerBoxCross 9 14 8 half_17_06_φ3) (75399026137/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (864692327/10000000000 : ℝ)) half_17_06_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_06_bounds3 l).1) (fun l => (half_17_06_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_06_total1, half_17_06_total2, half_17_06_total3, half_17_06_total4, half_17_06_total5, half_17_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_06) (half_15_06)
    (by simpa only [half_17_06_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_06_hx4)
  exact h.weaken (by norm_num [half_17_06_total1, half_17_06_total2, half_17_06_total3, half_17_06_total4, half_17_06_total5, half_17_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_06_hx2 : SourcePowerBound
    (powerBoxCross 9 15 4 half_17_06_φ2) (183020267909/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (494109901/5000000000 : ℝ)) half_17_06_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_06_bounds2 l).1) (fun l => (half_17_06_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_06_total1, half_17_06_total2, half_17_06_total3, half_17_06_total4, half_17_06_total5, half_17_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_06) (half_16_06)
    (by simpa only [half_17_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_06_hx3)
  exact h.weaken (by norm_num [half_17_06_total1, half_17_06_total2, half_17_06_total3, half_17_06_total4, half_17_06_total5, half_17_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_06_hx1 : SourcePowerBound
    (powerBoxCross 9 16 2 half_17_06_φ1) (220649283617/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (1035655147/10000000000 : ℝ)) half_17_06_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_06_bounds1 l).1) (fun l => (half_17_06_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_06_total1, half_17_06_total2, half_17_06_total3, half_17_06_total4, half_17_06_total5, half_17_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_06) (half_17_05)
    (by simpa only [half_17_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_06_hx2)
  exact h.weaken (by norm_num [half_17_06_total1, half_17_06_total2, half_17_06_total3, half_17_06_total4, half_17_06_total5, half_17_06_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_17_06 : AdmissibleExponent 9 34 (253465462947/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 15) (ψ := (105858643/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_16_06)
    (by simpa only [half_17_06_φ1] using half_17_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_06_total1, half_17_06_total2, half_17_06_total3, half_17_06_total4, half_17_06_total5, half_17_06_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_18_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1071001837/10000000000 : ℝ)

private theorem half_18_06_total1 : total half_18_06_φ1=(1071001837/10000000000 : ℝ) := by
  norm_num [half_18_06_φ1,total,emptyPhi,Fin.snoc]

private theorem half_18_06_bounds1 : ∀ l,0≤half_18_06_φ1 l ∧ half_18_06_φ1 l≤1 ∧
    0≤shiftExponents 9 half_18_06_φ1 l :=
  alternate_bounds_snoc emptyPhi (1071001837/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_18_06_φ2 : Fin 2 → ℝ := Fin.snoc half_18_06_φ1 (1053301921/10000000000 : ℝ)

private theorem half_18_06_total2 : total half_18_06_φ2=(1062151879/5000000000 : ℝ) := by
  change total (Fin.snoc half_18_06_φ1 (1053301921/10000000000 : ℝ))=(1062151879/5000000000 : ℝ)
  rw [alternate_total_snoc,half_18_06_total1]
  norm_num

private theorem half_18_06_bounds2 : ∀ l,0≤half_18_06_φ2 l ∧ half_18_06_φ2 l≤1 ∧
    0≤shiftExponents 9 half_18_06_φ2 l :=
  alternate_bounds_snoc half_18_06_φ1 (1053301921/10000000000 : ℝ) half_18_06_bounds1 (by norm_num)

private def half_18_06_φ3 : Fin 3 → ℝ := Fin.snoc half_18_06_φ2 (98446203/1000000000 : ℝ)

private theorem half_18_06_total3 : total half_18_06_φ3=(777191447/2500000000 : ℝ) := by
  change total (Fin.snoc half_18_06_φ2 (98446203/1000000000 : ℝ))=(777191447/2500000000 : ℝ)
  rw [alternate_total_snoc,half_18_06_total2]
  norm_num

private theorem half_18_06_bounds3 : ∀ l,0≤half_18_06_φ3 l ∧ half_18_06_φ3 l≤1 ∧
    0≤shiftExponents 9 half_18_06_φ3 l :=
  alternate_bounds_snoc half_18_06_φ2 (98446203/1000000000 : ℝ) half_18_06_bounds2 (by norm_num)

private def half_18_06_φ4 : Fin 4 → ℝ := Fin.snoc half_18_06_φ3 (215351069/2500000000 : ℝ)

private theorem half_18_06_total4 : total half_18_06_φ4=(248135629/625000000 : ℝ) := by
  change total (Fin.snoc half_18_06_φ3 (215351069/2500000000 : ℝ))=(248135629/625000000 : ℝ)
  rw [alternate_total_snoc,half_18_06_total3]
  norm_num

private theorem half_18_06_bounds4 : ∀ l,0≤half_18_06_φ4 l ∧ half_18_06_φ4 l≤1 ∧
    0≤shiftExponents 9 half_18_06_φ4 l :=
  alternate_bounds_snoc half_18_06_φ3 (215351069/2500000000 : ℝ) half_18_06_bounds3 (by norm_num)

private def half_18_06_φ5 : Fin 5 → ℝ := Fin.snoc half_18_06_φ4 (753728741/10000000000 : ℝ)

private theorem half_18_06_total5 : total half_18_06_φ5=(944779761/2000000000 : ℝ) := by
  change total (Fin.snoc half_18_06_φ4 (753728741/10000000000 : ℝ))=(944779761/2000000000 : ℝ)
  rw [alternate_total_snoc,half_18_06_total4]
  norm_num

private theorem half_18_06_bounds5 : ∀ l,0≤half_18_06_φ5 l ∧ half_18_06_φ5 l≤1 ∧
    0≤shiftExponents 9 half_18_06_φ5 l :=
  alternate_bounds_snoc half_18_06_φ4 (753728741/10000000000 : ℝ) half_18_06_bounds4 (by norm_num)

private def half_18_06_φ6 : Fin 6 → ℝ := Fin.snoc half_18_06_φ5 (659512649/10000000000 : ℝ)

private theorem half_18_06_total6 : total half_18_06_φ6=(2691705727/5000000000 : ℝ) := by
  change total (Fin.snoc half_18_06_φ5 (659512649/10000000000 : ℝ))=(2691705727/5000000000 : ℝ)
  rw [alternate_total_snoc,half_18_06_total5]
  norm_num

private theorem half_18_06_bounds6 : ∀ l,0≤half_18_06_φ6 l ∧ half_18_06_φ6 l≤1 ∧
    0≤shiftExponents 9 half_18_06_φ6 l :=
  alternate_bounds_snoc half_18_06_φ5 (659512649/10000000000 : ℝ) half_18_06_bounds5 (by norm_num)

private theorem half_18_06_prefix : PrefixCondition 9 half_18_06_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_18_06_φ1, half_18_06_φ2, half_18_06_φ3, half_18_06_φ4, half_18_06_φ5, half_18_06_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_18_06_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_18_06_φ6) (4424882819/625000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_18_06_φ6
    (fun i => (half_18_06_bounds6 i).1) (fun i => (half_18_06_bounds6 i).2.1)
    (fun i => (half_18_06_bounds6 i).2.2) half_18_06_prefix
  convert h using 1 <;> norm_num [half_18_06_total1, half_18_06_total2, half_18_06_total3, half_18_06_total4, half_18_06_total5, half_18_06_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_18_06_hx6 : SourcePowerBound
    (powerBoxCross 9 12 64 half_18_06_φ6) (98860692573/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 12) (r := 2) (v := 0) (w := 16) (D := 64)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_18_06_φ6 (by norm_num [half_18_06_total1, half_18_06_total2, half_18_06_total3, half_18_06_total4, half_18_06_total5, half_18_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_18_06_total1, half_18_06_total2, half_18_06_total3, half_18_06_total4, half_18_06_total5, half_18_06_total6, parameterExponent, curveLoss, dyadicExponent]) half_18_06_hF2
    (admissibleExponent_zero 9) (half_16_06)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_18_06_total1, half_18_06_total2, half_18_06_total3, half_18_06_total4, half_18_06_total5, half_18_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_06_hx5 : SourcePowerBound
    (powerBoxCross 9 13 32 half_18_06_φ5) (28780610489/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 13) (u := 11) (t := 14)
    (D := 32) (ψ := (659512649/10000000000 : ℝ)) half_18_06_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_06_bounds5 l).1) (fun l => (half_18_06_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_06_total1, half_18_06_total2, half_18_06_total3, half_18_06_total4, half_18_06_total5, half_18_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_06) (half_14_06)
    (by simpa only [half_18_06_φ6, show (2:ℝ)*32=64 by norm_num] using half_18_06_hx6)
  exact h.weaken (by norm_num [half_18_06_total1, half_18_06_total2, half_18_06_total3, half_18_06_total4, half_18_06_total5, half_18_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_06_hx4 : SourcePowerBound
    (powerBoxCross 9 14 16 half_18_06_φ4) (136105681673/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 14) (u := 12) (t := 15)
    (D := 16) (ψ := (753728741/10000000000 : ℝ)) half_18_06_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_06_bounds4 l).1) (fun l => (half_18_06_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_06_total1, half_18_06_total2, half_18_06_total3, half_18_06_total4, half_18_06_total5, half_18_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_06) (half_15_06)
    (by simpa only [half_18_06_φ5, show (2:ℝ)*16=32 by norm_num] using half_18_06_hx5)
  exact h.weaken (by norm_num [half_18_06_total1, half_18_06_total2, half_18_06_total3, half_18_06_total4, half_18_06_total5, half_18_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_06_hx3 : SourcePowerBound
    (powerBoxCross 9 15 8 half_18_06_φ3) (163013527577/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 15) (u := 13) (t := 16)
    (D := 8) (ψ := (215351069/2500000000 : ℝ)) half_18_06_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_06_bounds3 l).1) (fun l => (half_18_06_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_06_total1, half_18_06_total2, half_18_06_total3, half_18_06_total4, half_18_06_total5, half_18_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_06) (half_16_06)
    (by simpa only [half_18_06_φ4, show (2:ℝ)*8=16 by norm_num] using half_18_06_hx4)
  exact h.weaken (by norm_num [half_18_06_total1, half_18_06_total2, half_18_06_total3, half_18_06_total4, half_18_06_total5, half_18_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_06_hx2 : SourcePowerBound
    (powerBoxCross 9 16 4 half_18_06_φ2) (49273774473/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 16) (u := 14) (t := 17)
    (D := 4) (ψ := (98446203/1000000000 : ℝ)) half_18_06_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_06_bounds2 l).1) (fun l => (half_18_06_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_06_total1, half_18_06_total2, half_18_06_total3, half_18_06_total4, half_18_06_total5, half_18_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_06) (half_17_06)
    (by simpa only [half_18_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_18_06_hx3)
  exact h.weaken (by norm_num [half_18_06_total1, half_18_06_total2, half_18_06_total3, half_18_06_total4, half_18_06_total5, half_18_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_06_hx1 : SourcePowerBound
    (powerBoxCross 9 17 2 half_18_06_φ1) (47478053429/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 17) (u := 15) (t := 18)
    (D := 2) (ψ := (1053301921/10000000000 : ℝ)) half_18_06_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_06_bounds1 l).1) (fun l => (half_18_06_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_06_total1, half_18_06_total2, half_18_06_total3, half_18_06_total4, half_18_06_total5, half_18_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_06) (half_18_05)
    (by simpa only [half_18_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_18_06_hx2)
  exact h.weaken (by norm_num [half_18_06_total1, half_18_06_total2, half_18_06_total3, half_18_06_total4, half_18_06_total5, half_18_06_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_18_06 : AdmissibleExponent 9 36 (136366663883/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 16) (ψ := (1071001837/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_17_06)
    (by simpa only [half_18_06_φ1] using half_18_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_18_06_total1, half_18_06_total2, half_18_06_total3, half_18_06_total4, half_18_06_total5, half_18_06_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_19_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1080928859/10000000000 : ℝ)

private theorem half_19_06_total1 : total half_19_06_φ1=(1080928859/10000000000 : ℝ) := by
  norm_num [half_19_06_φ1,total,emptyPhi,Fin.snoc]

private theorem half_19_06_bounds1 : ∀ l,0≤half_19_06_φ1 l ∧ half_19_06_φ1 l≤1 ∧
    0≤shiftExponents 9 half_19_06_φ1 l :=
  alternate_bounds_snoc emptyPhi (1080928859/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_19_06_φ2 : Fin 2 → ℝ := Fin.snoc half_19_06_φ1 (1067108807/10000000000 : ℝ)

private theorem half_19_06_total2 : total half_19_06_φ2=(1074018833/5000000000 : ℝ) := by
  change total (Fin.snoc half_19_06_φ1 (1067108807/10000000000 : ℝ))=(1074018833/5000000000 : ℝ)
  rw [alternate_total_snoc,half_19_06_total1]
  norm_num

private theorem half_19_06_bounds2 : ∀ l,0≤half_19_06_φ2 l ∧ half_19_06_φ2 l≤1 ∧
    0≤shiftExponents 9 half_19_06_φ2 l :=
  alternate_bounds_snoc half_19_06_φ1 (1067108807/10000000000 : ℝ) half_19_06_bounds1 (by norm_num)

private def half_19_06_φ3 : Fin 3 → ℝ := Fin.snoc half_19_06_φ2 (981495291/10000000000 : ℝ)

private theorem half_19_06_total3 : total half_19_06_φ3=(3129532957/10000000000 : ℝ) := by
  change total (Fin.snoc half_19_06_φ2 (981495291/10000000000 : ℝ))=(3129532957/10000000000 : ℝ)
  rw [alternate_total_snoc,half_19_06_total2]
  norm_num

private theorem half_19_06_bounds3 : ∀ l,0≤half_19_06_φ3 l ∧ half_19_06_φ3 l≤1 ∧
    0≤shiftExponents 9 half_19_06_φ3 l :=
  alternate_bounds_snoc half_19_06_φ2 (981495291/10000000000 : ℝ) half_19_06_bounds2 (by norm_num)

private def half_19_06_φ4 : Fin 4 → ℝ := Fin.snoc half_19_06_φ3 (42940419/500000000 : ℝ)

private theorem half_19_06_total4 : total half_19_06_φ4=(3988341337/10000000000 : ℝ) := by
  change total (Fin.snoc half_19_06_φ3 (42940419/500000000 : ℝ))=(3988341337/10000000000 : ℝ)
  rw [alternate_total_snoc,half_19_06_total3]
  norm_num

private theorem half_19_06_bounds4 : ∀ l,0≤half_19_06_φ4 l ∧ half_19_06_φ4 l≤1 ∧
    0≤shiftExponents 9 half_19_06_φ4 l :=
  alternate_bounds_snoc half_19_06_φ3 (42940419/500000000 : ℝ) half_19_06_bounds3 (by norm_num)

private def half_19_06_φ5 : Fin 5 → ℝ := Fin.snoc half_19_06_φ4 (187864333/2500000000 : ℝ)

private theorem half_19_06_total5 : total half_19_06_φ5=(4739798669/10000000000 : ℝ) := by
  change total (Fin.snoc half_19_06_φ4 (187864333/2500000000 : ℝ))=(4739798669/10000000000 : ℝ)
  rw [alternate_total_snoc,half_19_06_total4]
  norm_num

private theorem half_19_06_bounds5 : ∀ l,0≤half_19_06_φ5 l ∧ half_19_06_φ5 l≤1 ∧
    0≤shiftExponents 9 half_19_06_φ5 l :=
  alternate_bounds_snoc half_19_06_φ4 (187864333/2500000000 : ℝ) half_19_06_bounds4 (by norm_num)

private def half_19_06_φ6 : Fin 6 → ℝ := Fin.snoc half_19_06_φ5 (328762583/5000000000 : ℝ)

private theorem half_19_06_total6 : total half_19_06_φ6=(1079464767/2000000000 : ℝ) := by
  change total (Fin.snoc half_19_06_φ5 (328762583/5000000000 : ℝ))=(1079464767/2000000000 : ℝ)
  rw [alternate_total_snoc,half_19_06_total5]
  norm_num

private theorem half_19_06_bounds6 : ∀ l,0≤half_19_06_φ6 l ∧ half_19_06_φ6 l≤1 ∧
    0≤shiftExponents 9 half_19_06_φ6 l :=
  alternate_bounds_snoc half_19_06_φ5 (328762583/5000000000 : ℝ) half_19_06_bounds5 (by norm_num)

private theorem half_19_06_prefix : PrefixCondition 9 half_19_06_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_19_06_φ1, half_19_06_φ2, half_19_06_φ3, half_19_06_φ4, half_19_06_φ5, half_19_06_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_19_06_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_19_06_φ6) (1761605699/250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_19_06_φ6
    (fun i => (half_19_06_bounds6 i).1) (fun i => (half_19_06_bounds6 i).2.1)
    (fun i => (half_19_06_bounds6 i).2.2) half_19_06_prefix
  convert h using 1 <;> norm_num [half_19_06_total1, half_19_06_total2, half_19_06_total3, half_19_06_total4, half_19_06_total5, half_19_06_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_19_06_hx6 : SourcePowerBound
    (powerBoxCross 9 13 64 half_19_06_φ6) (26832402229/2500000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 13) (r := 2) (v := 17) (w := 18) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_19_06_φ6 (by norm_num [half_19_06_total1, half_19_06_total2, half_19_06_total3, half_19_06_total4, half_19_06_total5, half_19_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_19_06_total1, half_19_06_total2, half_19_06_total3, half_19_06_total4, half_19_06_total5, half_19_06_total6, parameterExponent, curveLoss, dyadicExponent]) half_19_06_hF2
    (half_17_06) (half_18_06)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_19_06_total1, half_19_06_total2, half_19_06_total3, half_19_06_total4, half_19_06_total5, half_19_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_06_hx5 : SourcePowerBound
    (powerBoxCross 9 14 32 half_19_06_φ5) (778945993/62500000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 14) (u := 12) (t := 15)
    (D := 32) (ψ := (328762583/5000000000 : ℝ)) half_19_06_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_06_bounds5 l).1) (fun l => (half_19_06_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_06_total1, half_19_06_total2, half_19_06_total3, half_19_06_total4, half_19_06_total5, half_19_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_06) (half_15_06)
    (by simpa only [half_19_06_φ6, show (2:ℝ)*32=64 by norm_num] using half_19_06_hx6)
  exact h.weaken (by norm_num [half_19_06_total1, half_19_06_total2, half_19_06_total3, half_19_06_total4, half_19_06_total5, half_19_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_06_hx4 : SourcePowerBound
    (powerBoxCross 9 15 16 half_19_06_φ4) (146964959879/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 15) (u := 13) (t := 16)
    (D := 16) (ψ := (187864333/2500000000 : ℝ)) half_19_06_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_06_bounds4 l).1) (fun l => (half_19_06_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_06_total1, half_19_06_total2, half_19_06_total3, half_19_06_total4, half_19_06_total5, half_19_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_06) (half_16_06)
    (by simpa only [half_19_06_φ5, show (2:ℝ)*16=32 by norm_num] using half_19_06_hx5)
  exact h.weaken (by norm_num [half_19_06_total1, half_19_06_total2, half_19_06_total3, half_19_06_total4, half_19_06_total5, half_19_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_06_hx3 : SourcePowerBound
    (powerBoxCross 9 16 8 half_19_06_φ3) (43872093777/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 16) (u := 14) (t := 17)
    (D := 8) (ψ := (42940419/500000000 : ℝ)) half_19_06_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_06_bounds3 l).1) (fun l => (half_19_06_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_06_total1, half_19_06_total2, half_19_06_total3, half_19_06_total4, half_19_06_total5, half_19_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_06) (half_17_06)
    (by simpa only [half_19_06_φ4, show (2:ℝ)*8=16 by norm_num] using half_19_06_hx4)
  exact h.weaken (by norm_num [half_19_06_total1, half_19_06_total2, half_19_06_total3, half_19_06_total4, half_19_06_total5, half_19_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_06_hx2 : SourcePowerBound
    (powerBoxCross 9 17 4 half_19_06_φ2) (211439804743/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 17) (u := 15) (t := 18)
    (D := 4) (ψ := (981495291/10000000000 : ℝ)) half_19_06_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_06_bounds2 l).1) (fun l => (half_19_06_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_06_total1, half_19_06_total2, half_19_06_total3, half_19_06_total4, half_19_06_total5, half_19_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_06) (half_18_06)
    (by simpa only [half_19_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_19_06_hx3)
  exact h.weaken (by norm_num [half_19_06_total1, half_19_06_total2, half_19_06_total3, half_19_06_total4, half_19_06_total5, half_19_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_06_hx1 : SourcePowerBound
    (powerBoxCross 9 18 2 half_19_06_φ1) (63583431037/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 18) (u := 16) (t := 19)
    (D := 2) (ψ := (1067108807/10000000000 : ℝ)) half_19_06_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_06_bounds1 l).1) (fun l => (half_19_06_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_06_total1, half_19_06_total2, half_19_06_total3, half_19_06_total4, half_19_06_total5, half_19_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_06) (half_19_05)
    (by simpa only [half_19_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_19_06_hx2)
  exact h.weaken (by norm_num [half_19_06_total1, half_19_06_total2, half_19_06_total3, half_19_06_total4, half_19_06_total5, half_19_06_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_19_06 : AdmissibleExponent 9 38 (292166234213/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 17) (ψ := (1080928859/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_18_06)
    (by simpa only [half_19_06_φ1] using half_19_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_19_06_total1, half_19_06_total2, half_19_06_total3, half_19_06_total4, half_19_06_total5, half_19_06_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_20_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (54444827/500000000 : ℝ)

private theorem half_20_06_total1 : total half_20_06_φ1=(54444827/500000000 : ℝ) := by
  norm_num [half_20_06_φ1,total,emptyPhi,Fin.snoc]

private theorem half_20_06_bounds1 : ∀ l,0≤half_20_06_φ1 l ∧ half_20_06_φ1 l≤1 ∧
    0≤shiftExponents 9 half_20_06_φ1 l :=
  alternate_bounds_snoc emptyPhi (54444827/500000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_20_06_φ2 : Fin 2 → ℝ := Fin.snoc half_20_06_φ1 (215609061/2000000000 : ℝ)

private theorem half_20_06_total2 : total half_20_06_φ2=(433388369/2000000000 : ℝ) := by
  change total (Fin.snoc half_20_06_φ1 (215609061/2000000000 : ℝ))=(433388369/2000000000 : ℝ)
  rw [alternate_total_snoc,half_20_06_total1]
  norm_num

private theorem half_20_06_bounds2 : ∀ l,0≤half_20_06_φ2 l ∧ half_20_06_φ2 l≤1 ∧
    0≤shiftExponents 9 half_20_06_φ2 l :=
  alternate_bounds_snoc half_20_06_φ1 (215609061/2000000000 : ℝ) half_20_06_bounds1 (by norm_num)

private def half_20_06_φ3 : Fin 3 → ℝ := Fin.snoc half_20_06_φ2 (979132269/10000000000 : ℝ)

private theorem half_20_06_total3 : total half_20_06_φ3=(1573037057/5000000000 : ℝ) := by
  change total (Fin.snoc half_20_06_φ2 (979132269/10000000000 : ℝ))=(1573037057/5000000000 : ℝ)
  rw [alternate_total_snoc,half_20_06_total2]
  norm_num

private theorem half_20_06_bounds3 : ∀ l,0≤half_20_06_φ3 l ∧ half_20_06_φ3 l≤1 ∧
    0≤shiftExponents 9 half_20_06_φ3 l :=
  alternate_bounds_snoc half_20_06_φ2 (979132269/10000000000 : ℝ) half_20_06_bounds2 (by norm_num)

private def half_20_06_φ4 : Fin 4 → ℝ := Fin.snoc half_20_06_φ3 (171348147/2000000000 : ℝ)

private theorem half_20_06_total4 : total half_20_06_φ4=(4002814849/10000000000 : ℝ) := by
  change total (Fin.snoc half_20_06_φ3 (171348147/2000000000 : ℝ))=(4002814849/10000000000 : ℝ)
  rw [alternate_total_snoc,half_20_06_total3]
  norm_num

private theorem half_20_06_bounds4 : ∀ l,0≤half_20_06_φ4 l ∧ half_20_06_φ4 l≤1 ∧
    0≤shiftExponents 9 half_20_06_φ4 l :=
  alternate_bounds_snoc half_20_06_φ3 (171348147/2000000000 : ℝ) half_20_06_bounds3 (by norm_num)

private def half_20_06_φ5 : Fin 5 → ℝ := Fin.snoc half_20_06_φ4 (749648143/10000000000 : ℝ)

private theorem half_20_06_total5 : total half_20_06_φ5=(297028937/625000000 : ℝ) := by
  change total (Fin.snoc half_20_06_φ4 (749648143/10000000000 : ℝ))=(297028937/625000000 : ℝ)
  rw [alternate_total_snoc,half_20_06_total4]
  norm_num

private theorem half_20_06_bounds5 : ∀ l,0≤half_20_06_φ5 l ∧ half_20_06_φ5 l≤1 ∧
    0≤shiftExponents 9 half_20_06_φ5 l :=
  alternate_bounds_snoc half_20_06_φ4 (749648143/10000000000 : ℝ) half_20_06_bounds4 (by norm_num)

private def half_20_06_φ6 : Fin 6 → ℝ := Fin.snoc half_20_06_φ5 (5247537/80000000 : ℝ)

private theorem half_20_06_total6 : total half_20_06_φ6=(5408405117/10000000000 : ℝ) := by
  change total (Fin.snoc half_20_06_φ5 (5247537/80000000 : ℝ))=(5408405117/10000000000 : ℝ)
  rw [alternate_total_snoc,half_20_06_total5]
  norm_num

private theorem half_20_06_bounds6 : ∀ l,0≤half_20_06_φ6 l ∧ half_20_06_φ6 l≤1 ∧
    0≤shiftExponents 9 half_20_06_φ6 l :=
  alternate_bounds_snoc half_20_06_φ5 (5247537/80000000 : ℝ) half_20_06_bounds5 (by norm_num)

private theorem half_20_06_prefix : PrefixCondition 9 half_20_06_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_20_06_φ1, half_20_06_φ2, half_20_06_φ3, half_20_06_φ4, half_20_06_φ5, half_20_06_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_20_06_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_20_06_φ6) (8774784649/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_20_06_φ6
    (fun i => (half_20_06_bounds6 i).1) (fun i => (half_20_06_bounds6 i).2.1)
    (fun i => (half_20_06_bounds6 i).2.2) half_20_06_prefix
  convert h using 1 <;> norm_num [half_20_06_total1, half_20_06_total2, half_20_06_total3, half_20_06_total4, half_20_06_total5, half_20_06_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_20_06_hx6 : SourcePowerBound
    (powerBoxCross 9 14 64 half_20_06_φ6) (115932042403/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 14) (r := 2) (v := 18) (w := 19) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_20_06_φ6 (by norm_num [half_20_06_total1, half_20_06_total2, half_20_06_total3, half_20_06_total4, half_20_06_total5, half_20_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_20_06_total1, half_20_06_total2, half_20_06_total3, half_20_06_total4, half_20_06_total5, half_20_06_total6, parameterExponent, curveLoss, dyadicExponent]) half_20_06_hF2
    (half_18_06) (half_19_06)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_20_06_total1, half_20_06_total2, half_20_06_total3, half_20_06_total4, half_20_06_total5, half_20_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_06_hx5 : SourcePowerBound
    (powerBoxCross 9 15 32 half_20_06_φ5) (33578421147/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 15) (u := 13) (t := 16)
    (D := 32) (ψ := (5247537/80000000 : ℝ)) half_20_06_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_06_bounds5 l).1) (fun l => (half_20_06_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_06_total1, half_20_06_total2, half_20_06_total3, half_20_06_total4, half_20_06_total5, half_20_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_06) (half_16_06)
    (by simpa only [half_20_06_φ6, show (2:ℝ)*32=64 by norm_num] using half_20_06_hx6)
  exact h.weaken (by norm_num [half_20_06_total1, half_20_06_total2, half_20_06_total3, half_20_06_total4, half_20_06_total5, half_20_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_06_hx4 : SourcePowerBound
    (powerBoxCross 9 16 16 half_20_06_φ4) (79009723253/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 16) (u := 14) (t := 17)
    (D := 16) (ψ := (749648143/10000000000 : ℝ)) half_20_06_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_06_bounds4 l).1) (fun l => (half_20_06_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_06_total1, half_20_06_total2, half_20_06_total3, half_20_06_total4, half_20_06_total5, half_20_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_06) (half_17_06)
    (by simpa only [half_20_06_φ5, show (2:ℝ)*16=32 by norm_num] using half_20_06_hx5)
  exact h.weaken (by norm_num [half_20_06_total1, half_20_06_total2, half_20_06_total3, half_20_06_total4, half_20_06_total5, half_20_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_06_hx3 : SourcePowerBound
    (powerBoxCross 9 17 8 half_20_06_φ3) (47042402237/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 17) (u := 15) (t := 18)
    (D := 8) (ψ := (171348147/2000000000 : ℝ)) half_20_06_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_06_bounds3 l).1) (fun l => (half_20_06_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_06_total1, half_20_06_total2, half_20_06_total3, half_20_06_total4, half_20_06_total5, half_20_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_06) (half_18_06)
    (by simpa only [half_20_06_φ4, show (2:ℝ)*8=16 by norm_num] using half_20_06_hx4)
  exact h.weaken (by norm_num [half_20_06_total1, half_20_06_total2, half_20_06_total3, half_20_06_total4, half_20_06_total5, half_20_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_06_hx2 : SourcePowerBound
    (powerBoxCross 9 18 4 half_20_06_φ2) (226000474709/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 18) (u := 16) (t := 19)
    (D := 4) (ψ := (979132269/10000000000 : ℝ)) half_20_06_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_06_bounds2 l).1) (fun l => (half_20_06_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_06_total1, half_20_06_total2, half_20_06_total3, half_20_06_total4, half_20_06_total5, half_20_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_06) (half_19_06)
    (by simpa only [half_20_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_20_06_hx3)
  exact h.weaken (by norm_num [half_20_06_total1, half_20_06_total2, half_20_06_total3, half_20_06_total4, half_20_06_total5, half_20_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_06_hx1 : SourcePowerBound
    (powerBoxCross 9 19 2 half_20_06_φ1) (135720625303/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 19) (u := 17) (t := 20)
    (D := 2) (ψ := (215609061/2000000000 : ℝ)) half_20_06_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_06_bounds1 l).1) (fun l => (half_20_06_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_06_total1, half_20_06_total2, half_20_06_total3, half_20_06_total4, half_20_06_total5, half_20_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_06) (half_20_05)
    (by simpa only [half_20_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_20_06_hx2)
  exact h.weaken (by norm_num [half_20_06_total1, half_20_06_total2, half_20_06_total3, half_20_06_total4, half_20_06_total5, half_20_06_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_20_06 : AdmissibleExponent 9 40 (155865211293/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 18) (ψ := (54444827/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_19_06)
    (by simpa only [half_20_06_φ1] using half_20_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_20_06_total1, half_20_06_total2, half_20_06_total3, half_20_06_total4, half_20_06_total5, half_20_06_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_21_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (547835169/5000000000 : ℝ)

private theorem half_21_06_total1 : total half_21_06_φ1=(547835169/5000000000 : ℝ) := by
  norm_num [half_21_06_φ1,total,emptyPhi,Fin.snoc]

private theorem half_21_06_bounds1 : ∀ l,0≤half_21_06_φ1 l ∧ half_21_06_φ1 l≤1 ∧
    0≤shiftExponents 9 half_21_06_φ1 l :=
  alternate_bounds_snoc emptyPhi (547835169/5000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_21_06_φ2 : Fin 2 → ℝ := Fin.snoc half_21_06_φ1 (1086673667/10000000000 : ℝ)

private theorem half_21_06_total2 : total half_21_06_φ2=(436468801/2000000000 : ℝ) := by
  change total (Fin.snoc half_21_06_φ1 (1086673667/10000000000 : ℝ))=(436468801/2000000000 : ℝ)
  rw [alternate_total_snoc,half_21_06_total1]
  norm_num

private theorem half_21_06_bounds2 : ∀ l,0≤half_21_06_φ2 l ∧ half_21_06_φ2 l≤1 ∧
    0≤shiftExponents 9 half_21_06_φ2 l :=
  alternate_bounds_snoc half_21_06_φ1 (1086673667/10000000000 : ℝ) half_21_06_bounds1 (by norm_num)

private def half_21_06_φ3 : Fin 3 → ℝ := Fin.snoc half_21_06_φ2 (977206999/10000000000 : ℝ)

private theorem half_21_06_total3 : total half_21_06_φ3=(789887751/2500000000 : ℝ) := by
  change total (Fin.snoc half_21_06_φ2 (977206999/10000000000 : ℝ))=(789887751/2500000000 : ℝ)
  rw [alternate_total_snoc,half_21_06_total2]
  norm_num

private theorem half_21_06_bounds3 : ∀ l,0≤half_21_06_φ3 l ∧ half_21_06_φ3 l≤1 ∧
    0≤shiftExponents 9 half_21_06_φ3 l :=
  alternate_bounds_snoc half_21_06_φ2 (977206999/10000000000 : ℝ) half_21_06_bounds2 (by norm_num)

private def half_21_06_φ4 : Fin 4 → ℝ := Fin.snoc half_21_06_φ3 (213764031/2500000000 : ℝ)

private theorem half_21_06_total4 : total half_21_06_φ4=(501825891/1250000000 : ℝ) := by
  change total (Fin.snoc half_21_06_φ3 (213764031/2500000000 : ℝ))=(501825891/1250000000 : ℝ)
  rw [alternate_total_snoc,half_21_06_total3]
  norm_num

private theorem half_21_06_bounds4 : ∀ l,0≤half_21_06_φ4 l ∧ half_21_06_φ4 l≤1 ∧
    0≤shiftExponents 9 half_21_06_φ4 l :=
  alternate_bounds_snoc half_21_06_φ3 (213764031/2500000000 : ℝ) half_21_06_bounds3 (by norm_num)

private def half_21_06_φ5 : Fin 5 → ℝ := Fin.snoc half_21_06_φ4 (187043527/2500000000 : ℝ)

private theorem half_21_06_total5 : total half_21_06_φ5=(1190695309/2500000000 : ℝ) := by
  change total (Fin.snoc half_21_06_φ4 (187043527/2500000000 : ℝ))=(1190695309/2500000000 : ℝ)
  rw [alternate_total_snoc,half_21_06_total4]
  norm_num

private theorem half_21_06_bounds5 : ∀ l,0≤half_21_06_φ5 l ∧ half_21_06_φ5 l≤1 ∧
    0≤shiftExponents 9 half_21_06_φ5 l :=
  alternate_bounds_snoc half_21_06_φ4 (187043527/2500000000 : ℝ) half_21_06_bounds4 (by norm_num)

private def half_21_06_φ6 : Fin 6 → ℝ := Fin.snoc half_21_06_φ5 (130930469/2000000000 : ℝ)

private theorem half_21_06_total6 : total half_21_06_φ6=(5417433581/10000000000 : ℝ) := by
  change total (Fin.snoc half_21_06_φ5 (130930469/2000000000 : ℝ))=(5417433581/10000000000 : ℝ)
  rw [alternate_total_snoc,half_21_06_total5]
  norm_num

private theorem half_21_06_bounds6 : ∀ l,0≤half_21_06_φ6 l ∧ half_21_06_φ6 l≤1 ∧
    0≤shiftExponents 9 half_21_06_φ6 l :=
  alternate_bounds_snoc half_21_06_φ5 (130930469/2000000000 : ℝ) half_21_06_bounds5 (by norm_num)

private theorem half_21_06_prefix : PrefixCondition 9 half_21_06_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_21_06_φ1, half_21_06_φ2, half_21_06_φ3, half_21_06_φ4, half_21_06_φ5, half_21_06_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_21_06_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_21_06_φ6) (8747699257/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_21_06_φ6
    (fun i => (half_21_06_bounds6 i).1) (fun i => (half_21_06_bounds6 i).2.1)
    (fun i => (half_21_06_bounds6 i).2.2) half_21_06_prefix
  convert h using 1 <;> norm_num [half_21_06_total1, half_21_06_total2, half_21_06_total3, half_21_06_total4, half_21_06_total5, half_21_06_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_21_06_hx6 : SourcePowerBound
    (powerBoxCross 9 15 64 half_21_06_φ6) (124634800989/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 15) (r := 2) (v := 0) (w := 20) (D := 64)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_21_06_φ6 (by norm_num [half_21_06_total1, half_21_06_total2, half_21_06_total3, half_21_06_total4, half_21_06_total5, half_21_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_21_06_total1, half_21_06_total2, half_21_06_total3, half_21_06_total4, half_21_06_total5, half_21_06_total6, parameterExponent, curveLoss, dyadicExponent]) half_21_06_hF2
    (admissibleExponent_zero 9) (half_20_06)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_21_06_total1, half_21_06_total2, half_21_06_total3, half_21_06_total4, half_21_06_total5, half_21_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_06_hx5 : SourcePowerBound
    (powerBoxCross 9 16 32 half_21_06_φ5) (72065719241/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 16) (u := 14) (t := 17)
    (D := 32) (ψ := (130930469/2000000000 : ℝ)) half_21_06_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_06_bounds5 l).1) (fun l => (half_21_06_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_06_total1, half_21_06_total2, half_21_06_total3, half_21_06_total4, half_21_06_total5, half_21_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_06) (half_17_06)
    (by simpa only [half_21_06_φ6, show (2:ℝ)*32=64 by norm_num] using half_21_06_hx6)
  exact h.weaken (by norm_num [half_21_06_total1, half_21_06_total2, half_21_06_total3, half_21_06_total4, half_21_06_total5, half_21_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_06_hx4 : SourcePowerBound
    (powerBoxCross 9 17 16 half_21_06_φ4) (84612397601/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 17) (u := 15) (t := 18)
    (D := 16) (ψ := (187043527/2500000000 : ℝ)) half_21_06_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_06_bounds4 l).1) (fun l => (half_21_06_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_06_total1, half_21_06_total2, half_21_06_total3, half_21_06_total4, half_21_06_total5, half_21_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_06) (half_18_06)
    (by simpa only [half_21_06_φ5, show (2:ℝ)*16=32 by norm_num] using half_21_06_hx5)
  exact h.weaken (by norm_num [half_21_06_total1, half_21_06_total2, half_21_06_total3, half_21_06_total4, half_21_06_total5, half_21_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_06_hx3 : SourcePowerBound
    (powerBoxCross 9 18 8 half_21_06_φ3) (100505015403/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 18) (u := 16) (t := 19)
    (D := 8) (ψ := (213764031/2500000000 : ℝ)) half_21_06_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_06_bounds3 l).1) (fun l => (half_21_06_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_06_total1, half_21_06_total2, half_21_06_total3, half_21_06_total4, half_21_06_total5, half_21_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_06) (half_19_06)
    (by simpa only [half_21_06_φ4, show (2:ℝ)*8=16 by norm_num] using half_21_06_hx4)
  exact h.weaken (by norm_num [half_21_06_total1, half_21_06_total2, half_21_06_total3, half_21_06_total4, half_21_06_total5, half_21_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_06_hx2 : SourcePowerBound
    (powerBoxCross 9 19 4 half_21_06_φ2) (120363411107/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 19) (u := 17) (t := 20)
    (D := 4) (ψ := (977206999/10000000000 : ℝ)) half_21_06_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_06_bounds2 l).1) (fun l => (half_21_06_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_06_total1, half_21_06_total2, half_21_06_total3, half_21_06_total4, half_21_06_total5, half_21_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_06) (half_20_06)
    (by simpa only [half_21_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_21_06_hx3)
  exact h.weaken (by norm_num [half_21_06_total1, half_21_06_total2, half_21_06_total3, half_21_06_total4, half_21_06_total5, half_21_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_06_hx1 : SourcePowerBound
    (powerBoxCross 9 20 2 half_21_06_φ1) (288670715183/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 20) (u := 18) (t := 21)
    (D := 2) (ψ := (1086673667/10000000000 : ℝ)) half_21_06_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_06_bounds1 l).1) (fun l => (half_21_06_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_06_total1, half_21_06_total2, half_21_06_total3, half_21_06_total4, half_21_06_total5, half_21_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_19_06) (half_21_05)
    (by simpa only [half_21_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_21_06_hx2)
  exact h.weaken (by norm_num [half_21_06_total1, half_21_06_total2, half_21_06_total3, half_21_06_total4, half_21_06_total5, half_21_06_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_21_06 : AdmissibleExponent 9 42 (66280371673/2000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 19) (ψ := (547835169/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_20_06)
    (by simpa only [half_21_06_φ1] using half_21_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_21_06_total1, half_21_06_total2, half_21_06_total3, half_21_06_total4, half_21_06_total5, half_21_06_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_22_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (551036601/5000000000 : ℝ)

private theorem half_22_06_total1 : total half_22_06_φ1=(551036601/5000000000 : ℝ) := by
  norm_num [half_22_06_φ1,total,emptyPhi,Fin.snoc]

private theorem half_22_06_bounds1 : ∀ l,0≤half_22_06_φ1 l ∧ half_22_06_φ1 l≤1 ∧
    0≤shiftExponents 9 half_22_06_φ1 l :=
  alternate_bounds_snoc emptyPhi (551036601/5000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_22_06_φ2 : Fin 2 → ℝ := Fin.snoc half_22_06_φ1 (1093749373/10000000000 : ℝ)

private theorem half_22_06_total2 : total half_22_06_φ2=(87832903/400000000 : ℝ) := by
  change total (Fin.snoc half_22_06_φ1 (1093749373/10000000000 : ℝ))=(87832903/400000000 : ℝ)
  rw [alternate_total_snoc,half_22_06_total1]
  norm_num

private theorem half_22_06_bounds2 : ∀ l,0≤half_22_06_φ2 l ∧ half_22_06_φ2 l≤1 ∧
    0≤shiftExponents 9 half_22_06_φ2 l :=
  alternate_bounds_snoc half_22_06_φ1 (1093749373/10000000000 : ℝ) half_22_06_bounds1 (by norm_num)

private def half_22_06_φ3 : Fin 3 → ℝ := Fin.snoc half_22_06_φ2 (975522177/10000000000 : ℝ)

private theorem half_22_06_total3 : total half_22_06_φ3=(198209047/625000000 : ℝ) := by
  change total (Fin.snoc half_22_06_φ2 (975522177/10000000000 : ℝ))=(198209047/625000000 : ℝ)
  rw [alternate_total_snoc,half_22_06_total2]
  norm_num

private theorem half_22_06_bounds3 : ∀ l,0≤half_22_06_φ3 l ∧ half_22_06_φ3 l≤1 ∧
    0≤shiftExponents 9 half_22_06_φ3 l :=
  alternate_bounds_snoc half_22_06_φ2 (975522177/10000000000 : ℝ) half_22_06_bounds2 (by norm_num)

private def half_22_06_φ4 : Fin 4 → ℝ := Fin.snoc half_22_06_φ3 (170716381/2000000000 : ℝ)

private theorem half_22_06_total4 : total half_22_06_φ4=(4024926657/10000000000 : ℝ) := by
  change total (Fin.snoc half_22_06_φ3 (170716381/2000000000 : ℝ))=(4024926657/10000000000 : ℝ)
  rw [alternate_total_snoc,half_22_06_total3]
  norm_num

private theorem half_22_06_bounds4 : ∀ l,0≤half_22_06_φ4 l ∧ half_22_06_φ4 l≤1 ∧
    0≤shiftExponents 9 half_22_06_φ4 l :=
  alternate_bounds_snoc half_22_06_φ3 (170716381/2000000000 : ℝ) half_22_06_bounds3 (by norm_num)

private def half_22_06_φ5 : Fin 5 → ℝ := Fin.snoc half_22_06_φ4 (746884167/10000000000 : ℝ)

private theorem half_22_06_total5 : total half_22_06_φ5=(596476353/1250000000 : ℝ) := by
  change total (Fin.snoc half_22_06_φ4 (746884167/10000000000 : ℝ))=(596476353/1250000000 : ℝ)
  rw [alternate_total_snoc,half_22_06_total4]
  norm_num

private theorem half_22_06_bounds5 : ∀ l,0≤half_22_06_φ5 l ∧ half_22_06_φ5 l≤1 ∧
    0≤shiftExponents 9 half_22_06_φ5 l :=
  alternate_bounds_snoc half_22_06_φ4 (746884167/10000000000 : ℝ) half_22_06_bounds4 (by norm_num)

private def half_22_06_φ6 : Fin 6 → ℝ := Fin.snoc half_22_06_φ5 (326761823/5000000000 : ℝ)

private theorem half_22_06_total6 : total half_22_06_φ6=(542533447/1000000000 : ℝ) := by
  change total (Fin.snoc half_22_06_φ5 (326761823/5000000000 : ℝ))=(542533447/1000000000 : ℝ)
  rw [alternate_total_snoc,half_22_06_total5]
  norm_num

private theorem half_22_06_bounds6 : ∀ l,0≤half_22_06_φ6 l ∧ half_22_06_φ6 l≤1 ∧
    0≤shiftExponents 9 half_22_06_φ6 l :=
  alternate_bounds_snoc half_22_06_φ5 (326761823/5000000000 : ℝ) half_22_06_bounds5 (by norm_num)

private theorem half_22_06_prefix : PrefixCondition 9 half_22_06_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_22_06_φ1, half_22_06_φ2, half_22_06_φ3, half_22_06_φ4, half_22_06_φ5, half_22_06_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_22_06_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_22_06_φ6) (872399659/125000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_22_06_φ6
    (fun i => (half_22_06_bounds6 i).1) (fun i => (half_22_06_bounds6 i).2.1)
    (fun i => (half_22_06_bounds6 i).2.2) half_22_06_prefix
  convert h using 1 <;> norm_num [half_22_06_total1, half_22_06_total2, half_22_06_total3, half_22_06_total4, half_22_06_total5, half_22_06_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_22_06_hx6 : SourcePowerBound
    (powerBoxCross 9 16 64 half_22_06_φ6) (133425199027/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 16) (r := 2) (v := 21) (w := 22) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_22_06_φ6 (by norm_num [half_22_06_total1, half_22_06_total2, half_22_06_total3, half_22_06_total4, half_22_06_total5, half_22_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_22_06_total1, half_22_06_total2, half_22_06_total3, half_22_06_total4, half_22_06_total5, half_22_06_total6, parameterExponent, curveLoss, dyadicExponent]) half_22_06_hF2
    (half_21_06) (half_22_05)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_22_06_total1, half_22_06_total2, half_22_06_total3, half_22_06_total4, half_22_06_total5, half_22_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_06_hx5 : SourcePowerBound
    (powerBoxCross 9 17 32 half_22_06_φ5) (154050044339/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 17) (u := 15) (t := 18)
    (D := 32) (ψ := (326761823/5000000000 : ℝ)) half_22_06_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_06_bounds5 l).1) (fun l => (half_22_06_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_06_total1, half_22_06_total2, half_22_06_total3, half_22_06_total4, half_22_06_total5, half_22_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_06) (half_18_06)
    (by simpa only [half_22_06_φ6, show (2:ℝ)*32=64 by norm_num] using half_22_06_hx6)
  exact h.weaken (by norm_num [half_22_06_total1, half_22_06_total2, half_22_06_total3, half_22_06_total4, half_22_06_total5, half_22_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_06_hx4 : SourcePowerBound
    (powerBoxCross 9 18 16 half_22_06_φ4) (90267319093/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 18) (u := 16) (t := 19)
    (D := 16) (ψ := (746884167/10000000000 : ℝ)) half_22_06_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_06_bounds4 l).1) (fun l => (half_22_06_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_06_total1, half_22_06_total2, half_22_06_total3, half_22_06_total4, half_22_06_total5, half_22_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_06) (half_19_06)
    (by simpa only [half_22_06_φ5, show (2:ℝ)*16=32 by norm_num] using half_22_06_hx5)
  exact h.weaken (by norm_num [half_22_06_total1, half_22_06_total2, half_22_06_total3, half_22_06_total4, half_22_06_total5, half_22_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_06_hx3 : SourcePowerBound
    (powerBoxCross 9 19 8 half_22_06_φ3) (213954602731/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 19) (u := 17) (t := 20)
    (D := 8) (ψ := (170716381/2000000000 : ℝ)) half_22_06_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_06_bounds3 l).1) (fun l => (half_22_06_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_06_total1, half_22_06_total2, half_22_06_total3, half_22_06_total4, half_22_06_total5, half_22_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_06) (half_20_06)
    (by simpa only [half_22_06_φ4, show (2:ℝ)*8=16 by norm_num] using half_22_06_hx4)
  exact h.weaken (by norm_num [half_22_06_total1, half_22_06_total2, half_22_06_total3, half_22_06_total4, half_22_06_total5, half_22_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_06_hx2 : SourcePowerBound
    (powerBoxCross 9 20 4 half_22_06_φ2) (255557116423/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 20) (u := 18) (t := 21)
    (D := 4) (ψ := (975522177/10000000000 : ℝ)) half_22_06_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_06_bounds2 l).1) (fun l => (half_22_06_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_06_total1, half_22_06_total2, half_22_06_total3, half_22_06_total4, half_22_06_total5, half_22_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_19_06) (half_21_06)
    (by simpa only [half_22_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_22_06_hx3)
  exact h.weaken (by norm_num [half_22_06_total1, half_22_06_total2, half_22_06_total3, half_22_06_total4, half_22_06_total5, half_22_06_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_06_hx1 : SourcePowerBound
    (powerBoxCross 9 21 2 half_22_06_φ1) (305981020857/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 21) (u := 19) (t := 22)
    (D := 2) (ψ := (1093749373/10000000000 : ℝ)) half_22_06_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_06_bounds1 l).1) (fun l => (half_22_06_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_06_total1, half_22_06_total2, half_22_06_total3, half_22_06_total4, half_22_06_total5, half_22_06_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_20_06) (half_22_05)
    (by simpa only [half_22_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_22_06_hx2)
  exact h.weaken (by norm_num [half_22_06_total1, half_22_06_total2, half_22_06_total3, half_22_06_total4, half_22_06_total5, half_22_06_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_22_06 : AdmissibleExponent 9 44 (351166022139/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 20) (ψ := (551036601/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_21_06)
    (by simpa only [half_22_06_φ1] using half_22_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_22_06_total1, half_22_06_total2, half_22_06_total3, half_22_06_total4, half_22_06_total5, half_22_06_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_10_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (880695961/10000000000 : ℝ)

private theorem half_10_07_total1 : total half_10_07_φ1=(880695961/10000000000 : ℝ) := by
  norm_num [half_10_07_φ1,total,emptyPhi,Fin.snoc]

private theorem half_10_07_bounds1 : ∀ l,0≤half_10_07_φ1 l ∧ half_10_07_φ1 l≤1 ∧
    0≤shiftExponents 9 half_10_07_φ1 l :=
  alternate_bounds_snoc emptyPhi (880695961/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_10_07_φ2 : Fin 2 → ℝ := Fin.snoc half_10_07_φ1 (821570683/10000000000 : ℝ)

private theorem half_10_07_total2 : total half_10_07_φ2=(425566661/2500000000 : ℝ) := by
  change total (Fin.snoc half_10_07_φ1 (821570683/10000000000 : ℝ))=(425566661/2500000000 : ℝ)
  rw [alternate_total_snoc,half_10_07_total1]
  norm_num

private theorem half_10_07_bounds2 : ∀ l,0≤half_10_07_φ2 l ∧ half_10_07_φ2 l≤1 ∧
    0≤shiftExponents 9 half_10_07_φ2 l :=
  alternate_bounds_snoc half_10_07_φ1 (821570683/10000000000 : ℝ) half_10_07_bounds1 (by norm_num)

private def half_10_07_φ3 : Fin 3 → ℝ := Fin.snoc half_10_07_φ2 (179264133/2500000000 : ℝ)

private theorem half_10_07_total3 : total half_10_07_φ3=(302415397/1250000000 : ℝ) := by
  change total (Fin.snoc half_10_07_φ2 (179264133/2500000000 : ℝ))=(302415397/1250000000 : ℝ)
  rw [alternate_total_snoc,half_10_07_total2]
  norm_num

private theorem half_10_07_bounds3 : ∀ l,0≤half_10_07_φ3 l ∧ half_10_07_φ3 l≤1 ∧
    0≤shiftExponents 9 half_10_07_φ3 l :=
  alternate_bounds_snoc half_10_07_φ2 (179264133/2500000000 : ℝ) half_10_07_bounds2 (by norm_num)

private def half_10_07_φ4 : Fin 4 → ℝ := Fin.snoc half_10_07_φ3 (112561009/2500000000 : ℝ)

private theorem half_10_07_total4 : total half_10_07_φ4=(717391803/2500000000 : ℝ) := by
  change total (Fin.snoc half_10_07_φ3 (112561009/2500000000 : ℝ))=(717391803/2500000000 : ℝ)
  rw [alternate_total_snoc,half_10_07_total3]
  norm_num

private theorem half_10_07_bounds4 : ∀ l,0≤half_10_07_φ4 l ∧ half_10_07_φ4 l≤1 ∧
    0≤shiftExponents 9 half_10_07_φ4 l :=
  alternate_bounds_snoc half_10_07_φ3 (112561009/2500000000 : ℝ) half_10_07_bounds3 (by norm_num)

private theorem half_10_07_prefix : PrefixCondition 9 half_10_07_φ4 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_10_07_φ1, half_10_07_φ2, half_10_07_φ3, half_10_07_φ4, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_10_07_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 16 half_10_07_φ4) (2222824591/312500000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 9) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_07_φ4
    (fun i => (half_10_07_bounds4 i).1) (fun i => (half_10_07_bounds4 i).2.1)
    (fun i => (half_10_07_bounds4 i).2.2) half_10_07_prefix
  convert h using 1 <;> norm_num [half_10_07_total1, half_10_07_total2, half_10_07_total3, half_10_07_total4, parameterExponent, curveLoss, dyadicExponent]

private theorem half_10_07_hx4 : SourcePowerBound
    (powerBoxCross 9 6 16 half_10_07_φ4) (4321419607/625000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 6) (r := 2) (v := 0) (w := 8) (D := 16)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_10_07_φ4 (by norm_num [half_10_07_total1, half_10_07_total2, half_10_07_total3, half_10_07_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_10_07_total1, half_10_07_total2, half_10_07_total3, half_10_07_total4, parameterExponent, curveLoss, dyadicExponent]) half_10_07_hF2
    (admissibleExponent_zero 9) (SeedCompletionHigher9SimpleSeeds.degree9_half_8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_07_total1, half_10_07_total2, half_10_07_total3, half_10_07_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_10_07_hx3 : SourcePowerBound
    (powerBoxCross 9 7 8 half_10_07_φ3) (78772539767/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 7) (u := 5) (t := 8)
    (D := 8) (ψ := (112561009/2500000000 : ℝ)) half_10_07_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_10_07_bounds3 l).1) (fun l => (half_10_07_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_10_07_total1, half_10_07_total2, half_10_07_total3, half_10_07_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_6) (SeedCompletionHigher9SimpleSeeds.degree9_half_8)
    (by simpa only [half_10_07_φ4, show (2:ℝ)*8=16 by norm_num] using half_10_07_hx4)
  exact h.weaken (by norm_num [half_10_07_total1, half_10_07_total2, half_10_07_total3, half_10_07_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_10_07_hx2 : SourcePowerBound
    (powerBoxCross 9 8 4 half_10_07_φ2) (4673341421/500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (179264133/2500000000 : ℝ)) half_10_07_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_10_07_bounds2 l).1) (fun l => (half_10_07_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_10_07_total1, half_10_07_total2, half_10_07_total3, half_10_07_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_7) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_10_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_07_hx3)
  exact h.weaken (by norm_num [half_10_07_total1, half_10_07_total2, half_10_07_total3, half_10_07_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_10_07_hx1 : SourcePowerBound
    (powerBoxCross 9 9 2 half_10_07_φ1) (28123141183/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (821570683/10000000000 : ℝ)) half_10_07_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_10_07_bounds1 l).1) (fun l => (half_10_07_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_10_07_total1, half_10_07_total2, half_10_07_total3, half_10_07_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_06)
    (by simpa only [half_10_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_07_hx2)
  exact h.weaken (by norm_num [half_10_07_total1, half_10_07_total2, half_10_07_total3, half_10_07_total4, parameterExponent, curveLoss, dyadicExponent])

theorem half_10_07 : AdmissibleExponent 9 20 (127464396069/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 8) (ψ := (880695961/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_10_07_φ1] using half_10_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_07_total1, half_10_07_total2, half_10_07_total3, half_10_07_total4, parameterExponent, curveLoss, dyadicExponent])

private def half_11_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (916240091/10000000000 : ℝ)

private theorem half_11_07_total1 : total half_11_07_φ1=(916240091/10000000000 : ℝ) := by
  norm_num [half_11_07_φ1,total,emptyPhi,Fin.snoc]

private theorem half_11_07_bounds1 : ∀ l,0≤half_11_07_φ1 l ∧ half_11_07_φ1 l≤1 ∧
    0≤shiftExponents 9 half_11_07_φ1 l :=
  alternate_bounds_snoc emptyPhi (916240091/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_11_07_φ2 : Fin 2 → ℝ := Fin.snoc half_11_07_φ1 (865457067/10000000000 : ℝ)

private theorem half_11_07_total2 : total half_11_07_φ2=(890848579/5000000000 : ℝ) := by
  change total (Fin.snoc half_11_07_φ1 (865457067/10000000000 : ℝ))=(890848579/5000000000 : ℝ)
  rw [alternate_total_snoc,half_11_07_total1]
  norm_num

private theorem half_11_07_bounds2 : ∀ l,0≤half_11_07_φ2 l ∧ half_11_07_φ2 l≤1 ∧
    0≤shiftExponents 9 half_11_07_φ2 l :=
  alternate_bounds_snoc half_11_07_φ1 (865457067/10000000000 : ℝ) half_11_07_bounds1 (by norm_num)

private def half_11_07_φ3 : Fin 3 → ℝ := Fin.snoc half_11_07_φ2 (788150323/10000000000 : ℝ)

private theorem half_11_07_total3 : total half_11_07_φ3=(2569847481/10000000000 : ℝ) := by
  change total (Fin.snoc half_11_07_φ2 (788150323/10000000000 : ℝ))=(2569847481/10000000000 : ℝ)
  rw [alternate_total_snoc,half_11_07_total2]
  norm_num

private theorem half_11_07_bounds3 : ∀ l,0≤half_11_07_φ3 l ∧ half_11_07_φ3 l≤1 ∧
    0≤shiftExponents 9 half_11_07_φ3 l :=
  alternate_bounds_snoc half_11_07_φ2 (788150323/10000000000 : ℝ) half_11_07_bounds2 (by norm_num)

private def half_11_07_φ4 : Fin 4 → ℝ := Fin.snoc half_11_07_φ3 (624874323/10000000000 : ℝ)

private theorem half_11_07_total4 : total half_11_07_φ4=(798680451/2500000000 : ℝ) := by
  change total (Fin.snoc half_11_07_φ3 (624874323/10000000000 : ℝ))=(798680451/2500000000 : ℝ)
  rw [alternate_total_snoc,half_11_07_total3]
  norm_num

private theorem half_11_07_bounds4 : ∀ l,0≤half_11_07_φ4 l ∧ half_11_07_φ4 l≤1 ∧
    0≤shiftExponents 9 half_11_07_φ4 l :=
  alternate_bounds_snoc half_11_07_φ3 (624874323/10000000000 : ℝ) half_11_07_bounds3 (by norm_num)

private theorem half_11_07_prefix : PrefixCondition 9 half_11_07_φ4 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_11_07_φ1, half_11_07_φ2, half_11_07_φ3, half_11_07_φ4, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_11_07_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 16 half_11_07_φ4) (1978958647/312500000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 9) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_07_φ4
    (fun i => (half_11_07_bounds4 i).1) (fun i => (half_11_07_bounds4 i).2.1)
    (fun i => (half_11_07_bounds4 i).2.2) half_11_07_prefix
  convert h using 1 <;> norm_num [half_11_07_total1, half_11_07_total2, half_11_07_total3, half_11_07_total4, parameterExponent, curveLoss, dyadicExponent]

private theorem half_11_07_hx4 : SourcePowerBound
    (powerBoxCross 9 7 16 half_11_07_φ4) (3771567549/500000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 7) (r := 2) (v := 9) (w := 10) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_11_07_φ4 (by norm_num [half_11_07_total1, half_11_07_total2, half_11_07_total3, half_11_07_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_11_07_total1, half_11_07_total2, half_11_07_total3, half_11_07_total4, parameterExponent, curveLoss, dyadicExponent]) half_11_07_hF2
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_10_07)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_07_total1, half_11_07_total2, half_11_07_total3, half_11_07_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_11_07_hx3 : SourcePowerBound
    (powerBoxCross 9 8 8 half_11_07_φ3) (10986651933/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (624874323/10000000000 : ℝ)) half_11_07_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_11_07_bounds3 l).1) (fun l => (half_11_07_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_11_07_total1, half_11_07_total2, half_11_07_total3, half_11_07_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_7) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_11_07_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_07_hx4)
  exact h.weaken (by norm_num [half_11_07_total1, half_11_07_total2, half_11_07_total3, half_11_07_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_11_07_hx2 : SourcePowerBound
    (powerBoxCross 9 9 4 half_11_07_φ2) (52553998473/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (788150323/10000000000 : ℝ)) half_11_07_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_11_07_bounds2 l).1) (fun l => (half_11_07_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_11_07_total1, half_11_07_total2, half_11_07_total3, half_11_07_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_07)
    (by simpa only [half_11_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_07_hx3)
  exact h.weaken (by norm_num [half_11_07_total1, half_11_07_total2, half_11_07_total3, half_11_07_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_11_07_hx1 : SourcePowerBound
    (powerBoxCross 9 10 2 half_11_07_φ1) (6335091859/500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (865457067/10000000000 : ℝ)) half_11_07_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_11_07_bounds1 l).1) (fun l => (half_11_07_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_11_07_total1, half_11_07_total2, half_11_07_total3, half_11_07_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_06)
    (by simpa only [half_11_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_07_hx2)
  exact h.weaken (by norm_num [half_11_07_total1, half_11_07_total2, half_11_07_total3, half_11_07_total4, parameterExponent, curveLoss, dyadicExponent])

theorem half_11_07 : AdmissibleExponent 9 22 (144110398909/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 9) (ψ := (916240091/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_10_07)
    (by simpa only [half_11_07_φ1] using half_11_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_07_total1, half_11_07_total2, half_11_07_total3, half_11_07_total4, parameterExponent, curveLoss, dyadicExponent])

private def half_12_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (473932821/5000000000 : ℝ)

private theorem half_12_07_total1 : total half_12_07_φ1=(473932821/5000000000 : ℝ) := by
  norm_num [half_12_07_φ1,total,emptyPhi,Fin.snoc]

private theorem half_12_07_bounds1 : ∀ l,0≤half_12_07_φ1 l ∧ half_12_07_φ1 l≤1 ∧
    0≤shiftExponents 9 half_12_07_φ1 l :=
  alternate_bounds_snoc emptyPhi (473932821/5000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_12_07_φ2 : Fin 2 → ℝ := Fin.snoc half_12_07_φ1 (451668451/5000000000 : ℝ)

private theorem half_12_07_total2 : total half_12_07_φ2=(115700159/625000000 : ℝ) := by
  change total (Fin.snoc half_12_07_φ1 (451668451/5000000000 : ℝ))=(115700159/625000000 : ℝ)
  rw [alternate_total_snoc,half_12_07_total1]
  norm_num

private theorem half_12_07_bounds2 : ∀ l,0≤half_12_07_φ2 l ∧ half_12_07_φ2 l≤1 ∧
    0≤shiftExponents 9 half_12_07_φ2 l :=
  alternate_bounds_snoc half_12_07_φ1 (451668451/5000000000 : ℝ) half_12_07_bounds1 (by norm_num)

private def half_12_07_φ3 : Fin 3 → ℝ := Fin.snoc half_12_07_φ2 (840792393/10000000000 : ℝ)

private theorem half_12_07_total3 : total half_12_07_φ3=(2691994937/10000000000 : ℝ) := by
  change total (Fin.snoc half_12_07_φ2 (840792393/10000000000 : ℝ))=(2691994937/10000000000 : ℝ)
  rw [alternate_total_snoc,half_12_07_total2]
  norm_num

private theorem half_12_07_bounds3 : ∀ l,0≤half_12_07_φ3 l ∧ half_12_07_φ3 l≤1 ∧
    0≤shiftExponents 9 half_12_07_φ3 l :=
  alternate_bounds_snoc half_12_07_φ2 (840792393/10000000000 : ℝ) half_12_07_bounds2 (by norm_num)

private def half_12_07_φ4 : Fin 4 → ℝ := Fin.snoc half_12_07_φ3 (364020333/5000000000 : ℝ)

private theorem half_12_07_total4 : total half_12_07_φ4=(3420035603/10000000000 : ℝ) := by
  change total (Fin.snoc half_12_07_φ3 (364020333/5000000000 : ℝ))=(3420035603/10000000000 : ℝ)
  rw [alternate_total_snoc,half_12_07_total3]
  norm_num

private theorem half_12_07_bounds4 : ∀ l,0≤half_12_07_φ4 l ∧ half_12_07_φ4 l≤1 ∧
    0≤shiftExponents 9 half_12_07_φ4 l :=
  alternate_bounds_snoc half_12_07_φ3 (364020333/5000000000 : ℝ) half_12_07_bounds3 (by norm_num)

private def half_12_07_φ5 : Fin 5 → ℝ := Fin.snoc half_12_07_φ4 (225281957/5000000000 : ℝ)

private theorem half_12_07_total5 : total half_12_07_φ5=(3870599517/10000000000 : ℝ) := by
  change total (Fin.snoc half_12_07_φ4 (225281957/5000000000 : ℝ))=(3870599517/10000000000 : ℝ)
  rw [alternate_total_snoc,half_12_07_total4]
  norm_num

private theorem half_12_07_bounds5 : ∀ l,0≤half_12_07_φ5 l ∧ half_12_07_φ5 l≤1 ∧
    0≤shiftExponents 9 half_12_07_φ5 l :=
  alternate_bounds_snoc half_12_07_φ4 (225281957/5000000000 : ℝ) half_12_07_bounds4 (by norm_num)

private theorem half_12_07_prefix : PrefixCondition 9 half_12_07_φ5 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_12_07_φ1, half_12_07_φ2, half_12_07_φ3, half_12_07_φ4, half_12_07_φ5, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_12_07_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 32 half_12_07_φ5) (9638201449/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_12_07_φ5
    (fun i => (half_12_07_bounds5 i).1) (fun i => (half_12_07_bounds5 i).2.1)
    (fun i => (half_12_07_bounds5 i).2.2) half_12_07_prefix
  convert h using 1 <;> norm_num [half_12_07_total1, half_12_07_total2, half_12_07_total3, half_12_07_total4, half_12_07_total5, parameterExponent, curveLoss, dyadicExponent]

private theorem half_12_07_hx5 : SourcePowerBound
    (powerBoxCross 9 7 32 half_12_07_φ5) (7295684151/1000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 7) (r := 2) (v := 9) (w := 10) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_12_07_φ5 (by norm_num [half_12_07_total1, half_12_07_total2, half_12_07_total3, half_12_07_total4, half_12_07_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_12_07_total1, half_12_07_total2, half_12_07_total3, half_12_07_total4, half_12_07_total5, parameterExponent, curveLoss, dyadicExponent]) half_12_07_hF2
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_10_07)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_07_total1, half_12_07_total2, half_12_07_total3, half_12_07_total4, half_12_07_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_07_hx4 : SourcePowerBound
    (powerBoxCross 9 8 16 half_12_07_φ4) (2574549341/312500000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 8) (u := 6) (t := 9)
    (D := 16) (ψ := (225281957/5000000000 : ℝ)) half_12_07_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_07_bounds4 l).1) (fun l => (half_12_07_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_07_total1, half_12_07_total2, half_12_07_total3, half_12_07_total4, half_12_07_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_7) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_12_07_φ5, show (2:ℝ)*16=32 by norm_num] using half_12_07_hx5)
  exact h.weaken (by norm_num [half_12_07_total1, half_12_07_total2, half_12_07_total3, half_12_07_total4, half_12_07_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_07_hx3 : SourcePowerBound
    (powerBoxCross 9 9 8 half_12_07_φ3) (19492127459/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (364020333/5000000000 : ℝ)) half_12_07_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_07_bounds3 l).1) (fun l => (half_12_07_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_07_total1, half_12_07_total2, half_12_07_total3, half_12_07_total4, half_12_07_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_07)
    (by simpa only [half_12_07_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_07_hx4)
  exact h.weaken (by norm_num [half_12_07_total1, half_12_07_total2, half_12_07_total3, half_12_07_total4, half_12_07_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_07_hx2 : SourcePowerBound
    (powerBoxCross 9 10 4 half_12_07_φ2) (117188566413/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (840792393/10000000000 : ℝ)) half_12_07_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_07_bounds2 l).1) (fun l => (half_12_07_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_07_total1, half_12_07_total2, half_12_07_total3, half_12_07_total4, half_12_07_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_07)
    (by simpa only [half_12_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_07_hx3)
  exact h.weaken (by norm_num [half_12_07_total1, half_12_07_total2, half_12_07_total3, half_12_07_total4, half_12_07_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_07_hx1 : SourcePowerBound
    (powerBoxCross 9 11 2 half_12_07_φ1) (141398534977/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (451668451/5000000000 : ℝ)) half_12_07_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_07_bounds1 l).1) (fun l => (half_12_07_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_07_total1, half_12_07_total2, half_12_07_total3, half_12_07_total4, half_12_07_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_07) (half_12_06)
    (by simpa only [half_12_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_07_hx2)
  exact h.weaken (by norm_num [half_12_07_total1, half_12_07_total2, half_12_07_total3, half_12_07_total4, half_12_07_total5, parameterExponent, curveLoss, dyadicExponent])

theorem half_12_07 : AdmissibleExponent 9 24 (161303713459/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 10) (ψ := (473932821/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_11_07)
    (by simpa only [half_12_07_φ1] using half_12_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_07_total1, half_12_07_total2, half_12_07_total3, half_12_07_total4, half_12_07_total5, parameterExponent, curveLoss, dyadicExponent])

private def half_13_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (121963259/1250000000 : ℝ)

private theorem half_13_07_total1 : total half_13_07_φ1=(121963259/1250000000 : ℝ) := by
  norm_num [half_13_07_φ1,total,emptyPhi,Fin.snoc]

private theorem half_13_07_bounds1 : ∀ l,0≤half_13_07_φ1 l ∧ half_13_07_φ1 l≤1 ∧
    0≤shiftExponents 9 half_13_07_φ1 l :=
  alternate_bounds_snoc emptyPhi (121963259/1250000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_13_07_φ2 : Fin 2 → ℝ := Fin.snoc half_13_07_φ1 (935813117/10000000000 : ℝ)

private theorem half_13_07_total2 : total half_13_07_φ2=(1911519189/10000000000 : ℝ) := by
  change total (Fin.snoc half_13_07_φ1 (935813117/10000000000 : ℝ))=(1911519189/10000000000 : ℝ)
  rw [alternate_total_snoc,half_13_07_total1]
  norm_num

private theorem half_13_07_bounds2 : ∀ l,0≤half_13_07_φ2 l ∧ half_13_07_φ2 l≤1 ∧
    0≤shiftExponents 9 half_13_07_φ2 l :=
  alternate_bounds_snoc half_13_07_φ1 (935813117/10000000000 : ℝ) half_13_07_bounds1 (by norm_num)

private def half_13_07_φ3 : Fin 3 → ℝ := Fin.snoc half_13_07_φ2 (44129667/500000000 : ℝ)

private theorem half_13_07_total3 : total half_13_07_φ3=(2794112529/10000000000 : ℝ) := by
  change total (Fin.snoc half_13_07_φ2 (44129667/500000000 : ℝ))=(2794112529/10000000000 : ℝ)
  rw [alternate_total_snoc,half_13_07_total2]
  norm_num

private theorem half_13_07_bounds3 : ∀ l,0≤half_13_07_φ3 l ∧ half_13_07_φ3 l≤1 ∧
    0≤shiftExponents 9 half_13_07_φ3 l :=
  alternate_bounds_snoc half_13_07_φ2 (44129667/500000000 : ℝ) half_13_07_bounds2 (by norm_num)

private def half_13_07_φ4 : Fin 4 → ℝ := Fin.snoc half_13_07_φ3 (794684591/10000000000 : ℝ)

private theorem half_13_07_total4 : total half_13_07_φ4=(11214991/31250000 : ℝ) := by
  change total (Fin.snoc half_13_07_φ3 (794684591/10000000000 : ℝ))=(11214991/31250000 : ℝ)
  rw [alternate_total_snoc,half_13_07_total3]
  norm_num

private theorem half_13_07_bounds4 : ∀ l,0≤half_13_07_φ4 l ∧ half_13_07_φ4 l≤1 ∧
    0≤shiftExponents 9 half_13_07_φ4 l :=
  alternate_bounds_snoc half_13_07_φ3 (794684591/10000000000 : ℝ) half_13_07_bounds3 (by norm_num)

private def half_13_07_φ5 : Fin 5 → ℝ := Fin.snoc half_13_07_φ4 (24297891/400000000 : ℝ)

private theorem half_13_07_total5 : total half_13_07_φ5=(839248879/2000000000 : ℝ) := by
  change total (Fin.snoc half_13_07_φ4 (24297891/400000000 : ℝ))=(839248879/2000000000 : ℝ)
  rw [alternate_total_snoc,half_13_07_total4]
  norm_num

private theorem half_13_07_bounds5 : ∀ l,0≤half_13_07_φ5 l ∧ half_13_07_φ5 l≤1 ∧
    0≤shiftExponents 9 half_13_07_φ5 l :=
  alternate_bounds_snoc half_13_07_φ4 (24297891/400000000 : ℝ) half_13_07_bounds4 (by norm_num)

private theorem half_13_07_prefix : PrefixCondition 9 half_13_07_φ5 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_13_07_φ1, half_13_07_φ2, half_13_07_φ3, half_13_07_φ4, half_13_07_φ5, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_13_07_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 32 half_13_07_φ5) (1732253363/250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_13_07_φ5
    (fun i => (half_13_07_bounds5 i).1) (fun i => (half_13_07_bounds5 i).2.1)
    (fun i => (half_13_07_bounds5 i).2.2) half_13_07_prefix
  convert h using 1 <;> norm_num [half_13_07_total1, half_13_07_total2, half_13_07_total3, half_13_07_total4, half_13_07_total5, parameterExponent, curveLoss, dyadicExponent]

private theorem half_13_07_hx5 : SourcePowerBound
    (powerBoxCross 9 8 32 half_13_07_φ5) (77635915479/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 8) (r := 2) (v := 10) (w := 11) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_13_07_φ5 (by norm_num [half_13_07_total1, half_13_07_total2, half_13_07_total3, half_13_07_total4, half_13_07_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_13_07_total1, half_13_07_total2, half_13_07_total3, half_13_07_total4, half_13_07_total5, parameterExponent, curveLoss, dyadicExponent]) half_13_07_hF2
    (half_10_07) (half_11_07)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_07_total1, half_13_07_total2, half_13_07_total3, half_13_07_total4, half_13_07_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_07_hx4 : SourcePowerBound
    (powerBoxCross 9 9 16 half_13_07_φ4) (89878628981/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (24297891/400000000 : ℝ)) half_13_07_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_07_bounds4 l).1) (fun l => (half_13_07_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_07_total1, half_13_07_total2, half_13_07_total3, half_13_07_total4, half_13_07_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_07)
    (by simpa only [half_13_07_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_07_hx5)
  exact h.weaken (by norm_num [half_13_07_total1, half_13_07_total2, half_13_07_total3, half_13_07_total4, half_13_07_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_07_hx3 : SourcePowerBound
    (powerBoxCross 9 10 8 half_13_07_φ3) (21487969859/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (794684591/10000000000 : ℝ)) half_13_07_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_07_bounds3 l).1) (fun l => (half_13_07_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_07_total1, half_13_07_total2, half_13_07_total3, half_13_07_total4, half_13_07_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_07)
    (by simpa only [half_13_07_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_07_hx4)
  exact h.weaken (by norm_num [half_13_07_total1, half_13_07_total2, half_13_07_total3, half_13_07_total4, half_13_07_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_07_hx2 : SourcePowerBound
    (powerBoxCross 9 11 4 half_13_07_φ2) (5187743367/400000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (44129667/500000000 : ℝ)) half_13_07_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_07_bounds2 l).1) (fun l => (half_13_07_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_07_total1, half_13_07_total2, half_13_07_total3, half_13_07_total4, half_13_07_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_07) (half_12_07)
    (by simpa only [half_13_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_07_hx3)
  exact h.weaken (by norm_num [half_13_07_total1, half_13_07_total2, half_13_07_total3, half_13_07_total4, half_13_07_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_07_hx1 : SourcePowerBound
    (powerBoxCross 9 12 2 half_13_07_φ1) (156540918273/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (935813117/10000000000 : ℝ)) half_13_07_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_07_bounds1 l).1) (fun l => (half_13_07_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_07_total1, half_13_07_total2, half_13_07_total3, half_13_07_total4, half_13_07_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_07) (half_13_06)
    (by simpa only [half_13_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_07_hx2)
  exact h.weaken (by norm_num [half_13_07_total1, half_13_07_total2, half_13_07_total3, half_13_07_total4, half_13_07_total5, parameterExponent, curveLoss, dyadicExponent])

theorem half_13_07 : AdmissibleExponent 9 26 (178982157929/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 11) (ψ := (121963259/1250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_12_07)
    (by simpa only [half_13_07_φ1] using half_13_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_07_total1, half_13_07_total2, half_13_07_total3, half_13_07_total4, half_13_07_total5, parameterExponent, curveLoss, dyadicExponent])

private def half_14_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1001003177/10000000000 : ℝ)

private theorem half_14_07_total1 : total half_14_07_φ1=(1001003177/10000000000 : ℝ) := by
  norm_num [half_14_07_φ1,total,emptyPhi,Fin.snoc]

private theorem half_14_07_bounds1 : ∀ l,0≤half_14_07_φ1 l ∧ half_14_07_φ1 l≤1 ∧
    0≤shiftExponents 9 half_14_07_φ1 l :=
  alternate_bounds_snoc emptyPhi (1001003177/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_14_07_φ2 : Fin 2 → ℝ := Fin.snoc half_14_07_φ1 (965443209/10000000000 : ℝ)

private theorem half_14_07_total2 : total half_14_07_φ2=(983223193/5000000000 : ℝ) := by
  change total (Fin.snoc half_14_07_φ1 (965443209/10000000000 : ℝ))=(983223193/5000000000 : ℝ)
  rw [alternate_total_snoc,half_14_07_total1]
  norm_num

private theorem half_14_07_bounds2 : ∀ l,0≤half_14_07_φ2 l ∧ half_14_07_φ2 l≤1 ∧
    0≤shiftExponents 9 half_14_07_φ2 l :=
  alternate_bounds_snoc half_14_07_φ1 (965443209/10000000000 : ℝ) half_14_07_bounds1 (by norm_num)

private def half_14_07_φ3 : Fin 3 → ℝ := Fin.snoc half_14_07_φ2 (920843693/10000000000 : ℝ)

private theorem half_14_07_total3 : total half_14_07_φ3=(2887290079/10000000000 : ℝ) := by
  change total (Fin.snoc half_14_07_φ2 (920843693/10000000000 : ℝ))=(2887290079/10000000000 : ℝ)
  rw [alternate_total_snoc,half_14_07_total2]
  norm_num

private theorem half_14_07_bounds3 : ∀ l,0≤half_14_07_φ3 l ∧ half_14_07_φ3 l≤1 ∧
    0≤shiftExponents 9 half_14_07_φ3 l :=
  alternate_bounds_snoc half_14_07_φ2 (920843693/10000000000 : ℝ) half_14_07_bounds2 (by norm_num)

private def half_14_07_φ4 : Fin 4 → ℝ := Fin.snoc half_14_07_φ3 (852808717/10000000000 : ℝ)

private theorem half_14_07_total4 : total half_14_07_φ4=(935024699/2500000000 : ℝ) := by
  change total (Fin.snoc half_14_07_φ3 (852808717/10000000000 : ℝ))=(935024699/2500000000 : ℝ)
  rw [alternate_total_snoc,half_14_07_total3]
  norm_num

private theorem half_14_07_bounds4 : ∀ l,0≤half_14_07_φ4 l ∧ half_14_07_φ4 l≤1 ∧
    0≤shiftExponents 9 half_14_07_φ4 l :=
  alternate_bounds_snoc half_14_07_φ3 (852808717/10000000000 : ℝ) half_14_07_bounds3 (by norm_num)

private def half_14_07_φ5 : Fin 5 → ℝ := Fin.snoc half_14_07_φ4 (362436223/5000000000 : ℝ)

private theorem half_14_07_total5 : total half_14_07_φ5=(2232485621/5000000000 : ℝ) := by
  change total (Fin.snoc half_14_07_φ4 (362436223/5000000000 : ℝ))=(2232485621/5000000000 : ℝ)
  rw [alternate_total_snoc,half_14_07_total4]
  norm_num

private theorem half_14_07_bounds5 : ∀ l,0≤half_14_07_φ5 l ∧ half_14_07_φ5 l≤1 ∧
    0≤shiftExponents 9 half_14_07_φ5 l :=
  alternate_bounds_snoc half_14_07_φ4 (362436223/5000000000 : ℝ) half_14_07_bounds4 (by norm_num)

private def half_14_07_φ6 : Fin 6 → ℝ := Fin.snoc half_14_07_φ5 (209966843/5000000000 : ℝ)

private theorem half_14_07_total6 : total half_14_07_φ6=(152653279/312500000 : ℝ) := by
  change total (Fin.snoc half_14_07_φ5 (209966843/5000000000 : ℝ))=(152653279/312500000 : ℝ)
  rw [alternate_total_snoc,half_14_07_total5]
  norm_num

private theorem half_14_07_bounds6 : ∀ l,0≤half_14_07_φ6 l ∧ half_14_07_φ6 l≤1 ∧
    0≤shiftExponents 9 half_14_07_φ6 l :=
  alternate_bounds_snoc half_14_07_φ5 (209966843/5000000000 : ℝ) half_14_07_bounds5 (by norm_num)

private theorem half_14_07_prefix : PrefixCondition 9 half_14_07_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_14_07_φ1, half_14_07_φ2, half_14_07_φ3, half_14_07_φ4, half_14_07_φ5, half_14_07_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_14_07_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_14_07_φ6) (323290163/39062500 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_14_07_φ6
    (fun i => (half_14_07_bounds6 i).1) (fun i => (half_14_07_bounds6 i).2.1)
    (fun i => (half_14_07_bounds6 i).2.2) half_14_07_prefix
  convert h using 1 <;> norm_num [half_14_07_total1, half_14_07_total2, half_14_07_total3, half_14_07_total4, half_14_07_total5, half_14_07_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_14_07_hF1 : SourcePowerBound
    (paddedMoment 9 0 1 64 half_14_07_φ6) (120784221/39062500 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_14_07_φ6
    (fun i => (half_14_07_bounds6 i).1) (fun i => (half_14_07_bounds6 i).2.1)
    (fun i => (half_14_07_bounds6 i).2.2) half_14_07_prefix
  convert h using 1 <;> norm_num [half_14_07_total1, half_14_07_total2, half_14_07_total3, half_14_07_total4, half_14_07_total5, half_14_07_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_14_07_hx6 : SourcePowerBound
    (powerBoxCross 9 8 64 half_14_07_φ6) (36912581711/5000000000 : ℝ) := by
  have h := full_B_cross_power (k := 9) (s := 8) (r := 1) (v := 2) (t := 11) (D := 64)
    (a := (1/22 : ℝ)) (b := (5/22 : ℝ)) (c := (8/11 : ℝ))
    (by norm_num) half_14_07_φ6 (by norm_num [half_14_07_total1, half_14_07_total2, half_14_07_total3, half_14_07_total4, half_14_07_total5, half_14_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_14_07_total1, half_14_07_total2, half_14_07_total3, half_14_07_total4, half_14_07_total5, half_14_07_total6, parameterExponent, curveLoss, dyadicExponent]) half_14_07_hF1 half_14_07_hF2
    (half_11_07)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_07_total1, half_14_07_total2, half_14_07_total3, half_14_07_total4, half_14_07_total5, half_14_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_07_hx5 : SourcePowerBound
    (powerBoxCross 9 9 32 half_14_07_φ5) (41239077141/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 9) (u := 7) (t := 10)
    (D := 32) (ψ := (209966843/5000000000 : ℝ)) half_14_07_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_07_bounds5 l).1) (fun l => (half_14_07_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_07_total1, half_14_07_total2, half_14_07_total3, half_14_07_total4, half_14_07_total5, half_14_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_07)
    (by simpa only [half_14_07_φ6, show (2:ℝ)*32=64 by norm_num] using half_14_07_hx6)
  exact h.weaken (by norm_num [half_14_07_total1, half_14_07_total2, half_14_07_total3, half_14_07_total4, half_14_07_total5, half_14_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_07_hx4 : SourcePowerBound
    (powerBoxCross 9 10 16 half_14_07_φ4) (9754594073/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (362436223/5000000000 : ℝ)) half_14_07_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_07_bounds4 l).1) (fun l => (half_14_07_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_07_total1, half_14_07_total2, half_14_07_total3, half_14_07_total4, half_14_07_total5, half_14_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_07)
    (by simpa only [half_14_07_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_07_hx5)
  exact h.weaken (by norm_num [half_14_07_total1, half_14_07_total2, half_14_07_total3, half_14_07_total4, half_14_07_total5, half_14_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_07_hx3 : SourcePowerBound
    (powerBoxCross 9 11 8 half_14_07_φ3) (29422704753/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (852808717/10000000000 : ℝ)) half_14_07_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_07_bounds3 l).1) (fun l => (half_14_07_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_07_total1, half_14_07_total2, half_14_07_total3, half_14_07_total4, half_14_07_total5, half_14_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_07) (half_12_07)
    (by simpa only [half_14_07_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_07_hx4)
  exact h.weaken (by norm_num [half_14_07_total1, half_14_07_total2, half_14_07_total3, half_14_07_total4, half_14_07_total5, half_14_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_07_hx2 : SourcePowerBound
    (powerBoxCross 9 12 4 half_14_07_φ2) (142541620823/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (920843693/10000000000 : ℝ)) half_14_07_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_07_bounds2 l).1) (fun l => (half_14_07_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_07_total1, half_14_07_total2, half_14_07_total3, half_14_07_total4, half_14_07_total5, half_14_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_07) (half_13_07)
    (by simpa only [half_14_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_07_hx3)
  exact h.weaken (by norm_num [half_14_07_total1, half_14_07_total2, half_14_07_total3, half_14_07_total4, half_14_07_total5, half_14_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_07_hx1 : SourcePowerBound
    (powerBoxCross 9 13 2 half_14_07_φ1) (172066990241/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (965443209/10000000000 : ℝ)) half_14_07_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_07_bounds1 l).1) (fun l => (half_14_07_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_07_total1, half_14_07_total2, half_14_07_total3, half_14_07_total4, half_14_07_total5, half_14_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_07) (half_14_06)
    (by simpa only [half_14_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_07_hx2)
  exact h.weaken (by norm_num [half_14_07_total1, half_14_07_total2, half_14_07_total3, half_14_07_total4, half_14_07_total5, half_14_07_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_14_07 : AdmissibleExponent 9 28 (98546034833/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 12) (ψ := (1001003177/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_13_07)
    (by simpa only [half_14_07_φ1] using half_14_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_07_total1, half_14_07_total2, half_14_07_total3, half_14_07_total4, half_14_07_total5, half_14_07_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_15_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1021575389/10000000000 : ℝ)

private theorem half_15_07_total1 : total half_15_07_φ1=(1021575389/10000000000 : ℝ) := by
  norm_num [half_15_07_φ1,total,emptyPhi,Fin.snoc]

private theorem half_15_07_bounds1 : ∀ l,0≤half_15_07_φ1 l ∧ half_15_07_φ1 l≤1 ∧
    0≤shiftExponents 9 half_15_07_φ1 l :=
  alternate_bounds_snoc emptyPhi (1021575389/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_15_07_φ2 : Fin 2 → ℝ := Fin.snoc half_15_07_φ1 (990540737/10000000000 : ℝ)

private theorem half_15_07_total2 : total half_15_07_φ2=(1006058063/5000000000 : ℝ) := by
  change total (Fin.snoc half_15_07_φ1 (990540737/10000000000 : ℝ))=(1006058063/5000000000 : ℝ)
  rw [alternate_total_snoc,half_15_07_total1]
  norm_num

private theorem half_15_07_bounds2 : ∀ l,0≤half_15_07_φ2 l ∧ half_15_07_φ2 l≤1 ∧
    0≤shiftExponents 9 half_15_07_φ2 l :=
  alternate_bounds_snoc half_15_07_φ1 (990540737/10000000000 : ℝ) half_15_07_bounds1 (by norm_num)

private def half_15_07_φ3 : Fin 3 → ℝ := Fin.snoc half_15_07_φ2 (475567689/5000000000 : ℝ)

private theorem half_15_07_total3 : total half_15_07_φ3=(185203219/625000000 : ℝ) := by
  change total (Fin.snoc half_15_07_φ2 (475567689/5000000000 : ℝ))=(185203219/625000000 : ℝ)
  rw [alternate_total_snoc,half_15_07_total2]
  norm_num

private theorem half_15_07_bounds3 : ∀ l,0≤half_15_07_φ3 l ∧ half_15_07_φ3 l≤1 ∧
    0≤shiftExponents 9 half_15_07_φ3 l :=
  alternate_bounds_snoc half_15_07_φ2 (475567689/5000000000 : ℝ) half_15_07_bounds2 (by norm_num)

private def half_15_07_φ4 : Fin 4 → ℝ := Fin.snoc half_15_07_φ3 (879593561/10000000000 : ℝ)

private theorem half_15_07_total4 : total half_15_07_φ4=(768569013/2000000000 : ℝ) := by
  change total (Fin.snoc half_15_07_φ3 (879593561/10000000000 : ℝ))=(768569013/2000000000 : ℝ)
  rw [alternate_total_snoc,half_15_07_total3]
  norm_num

private theorem half_15_07_bounds4 : ∀ l,0≤half_15_07_φ4 l ∧ half_15_07_φ4 l≤1 ∧
    0≤shiftExponents 9 half_15_07_φ4 l :=
  alternate_bounds_snoc half_15_07_φ3 (879593561/10000000000 : ℝ) half_15_07_bounds3 (by norm_num)

private def half_15_07_φ5 : Fin 5 → ℝ := Fin.snoc half_15_07_φ4 (384822183/5000000000 : ℝ)

private theorem half_15_07_total5 : total half_15_07_φ5=(4612489431/10000000000 : ℝ) := by
  change total (Fin.snoc half_15_07_φ4 (384822183/5000000000 : ℝ))=(4612489431/10000000000 : ℝ)
  rw [alternate_total_snoc,half_15_07_total4]
  norm_num

private theorem half_15_07_bounds5 : ∀ l,0≤half_15_07_φ5 l ∧ half_15_07_φ5 l≤1 ∧
    0≤shiftExponents 9 half_15_07_φ5 l :=
  alternate_bounds_snoc half_15_07_φ4 (384822183/5000000000 : ℝ) half_15_07_bounds4 (by norm_num)

private def half_15_07_φ6 : Fin 6 → ℝ := Fin.snoc half_15_07_φ5 (549514319/10000000000 : ℝ)

private theorem half_15_07_total6 : total half_15_07_φ6=(4129603/8000000 : ℝ) := by
  change total (Fin.snoc half_15_07_φ5 (549514319/10000000000 : ℝ))=(4129603/8000000 : ℝ)
  rw [alternate_total_snoc,half_15_07_total5]
  norm_num

private theorem half_15_07_bounds6 : ∀ l,0≤half_15_07_φ6 l ∧ half_15_07_φ6 l≤1 ∧
    0≤shiftExponents 9 half_15_07_φ6 l :=
  alternate_bounds_snoc half_15_07_φ5 (549514319/10000000000 : ℝ) half_15_07_bounds5 (by norm_num)

private theorem half_15_07_prefix : PrefixCondition 9 half_15_07_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_15_07_φ1, half_15_07_φ2, half_15_07_φ3, half_15_07_φ4, half_15_07_φ5, half_15_07_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_15_07_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_15_07_φ6) (7611191/1000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_15_07_φ6
    (fun i => (half_15_07_bounds6 i).1) (fun i => (half_15_07_bounds6 i).2.1)
    (fun i => (half_15_07_bounds6 i).2.2) half_15_07_prefix
  convert h using 1 <;> norm_num [half_15_07_total1, half_15_07_total2, half_15_07_total3, half_15_07_total4, half_15_07_total5, half_15_07_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_15_07_hx6 : SourcePowerBound
    (powerBoxCross 9 9 64 half_15_07_φ6) (38778492281/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 9) (r := 2) (v := 0) (w := 12) (D := 64)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_15_07_φ6 (by norm_num [half_15_07_total1, half_15_07_total2, half_15_07_total3, half_15_07_total4, half_15_07_total5, half_15_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_15_07_total1, half_15_07_total2, half_15_07_total3, half_15_07_total4, half_15_07_total5, half_15_07_total6, parameterExponent, curveLoss, dyadicExponent]) half_15_07_hF2
    (admissibleExponent_zero 9) (half_12_07)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_07_total1, half_15_07_total2, half_15_07_total3, half_15_07_total4, half_15_07_total5, half_15_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_07_hx5 : SourcePowerBound
    (powerBoxCross 9 10 32 half_15_07_φ5) (8881922113/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 10) (u := 8) (t := 11)
    (D := 32) (ψ := (549514319/10000000000 : ℝ)) half_15_07_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_07_bounds5 l).1) (fun l => (half_15_07_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_07_total1, half_15_07_total2, half_15_07_total3, half_15_07_total4, half_15_07_total5, half_15_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_07)
    (by simpa only [half_15_07_φ6, show (2:ℝ)*32=64 by norm_num] using half_15_07_hx6)
  exact h.weaken (by norm_num [half_15_07_total1, half_15_07_total2, half_15_07_total3, half_15_07_total4, half_15_07_total5, half_15_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_07_hx4 : SourcePowerBound
    (powerBoxCross 9 11 16 half_15_07_φ4) (2120168991/200000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (384822183/5000000000 : ℝ)) half_15_07_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_07_bounds4 l).1) (fun l => (half_15_07_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_07_total1, half_15_07_total2, half_15_07_total3, half_15_07_total4, half_15_07_total5, half_15_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_07) (half_12_07)
    (by simpa only [half_15_07_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_07_hx5)
  exact h.weaken (by norm_num [half_15_07_total1, half_15_07_total2, half_15_07_total3, half_15_07_total4, half_15_07_total5, half_15_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_07_hx3 : SourcePowerBound
    (powerBoxCross 9 12 8 half_15_07_φ3) (128359572681/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (879593561/10000000000 : ℝ)) half_15_07_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_07_bounds3 l).1) (fun l => (half_15_07_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_07_total1, half_15_07_total2, half_15_07_total3, half_15_07_total4, half_15_07_total5, half_15_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_07) (half_13_07)
    (by simpa only [half_15_07_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_07_hx4)
  exact h.weaken (by norm_num [half_15_07_total1, half_15_07_total2, half_15_07_total3, half_15_07_total4, half_15_07_total5, half_15_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_07_hx2 : SourcePowerBound
    (powerBoxCross 9 13 4 half_15_07_φ2) (155786806933/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (475567689/5000000000 : ℝ)) half_15_07_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_07_bounds2 l).1) (fun l => (half_15_07_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_07_total1, half_15_07_total2, half_15_07_total3, half_15_07_total4, half_15_07_total5, half_15_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_07) (half_14_07)
    (by simpa only [half_15_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_07_hx3)
  exact h.weaken (by norm_num [half_15_07_total1, half_15_07_total2, half_15_07_total3, half_15_07_total4, half_15_07_total5, half_15_07_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_07_hx1 : SourcePowerBound
    (powerBoxCross 9 14 2 half_15_07_φ1) (46994801071/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (990540737/10000000000 : ℝ)) half_15_07_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_07_bounds1 l).1) (fun l => (half_15_07_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_07_total1, half_15_07_total2, half_15_07_total3, half_15_07_total4, half_15_07_total5, half_15_07_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_07) (half_15_06)
    (by simpa only [half_15_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_07_hx2)
  exact h.weaken (by norm_num [half_15_07_total1, half_15_07_total2, half_15_07_total3, half_15_07_total4, half_15_07_total5, half_15_07_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_15_07 : AdmissibleExponent 9 30 (215561739787/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 13) (ψ := (1021575389/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_14_07)
    (by simpa only [half_15_07_φ1] using half_15_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_07_total1, half_15_07_total2, half_15_07_total3, half_15_07_total4, half_15_07_total5, half_15_07_total6, parameterExponent, curveLoss, dyadicExponent])

end Waring.SeedCompletionAlternate9Seeds
