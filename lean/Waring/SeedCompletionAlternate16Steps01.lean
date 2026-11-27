import Waring.SeedCompletionAlternate16Arithmetic

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionAlternate16Seeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges SeedCompletionDivisorPowerScales
open PolicyCompletionSharpResidualSource

theorem half_15_00 : AdmissibleExponent 16 30 (37544927449/2000000000 : ℝ) := by
  have h := endpoint_admissible (s := 13) (by norm_num : 0 < (16 : ℕ))
    (SeedCompletionHigher16SimpleSeeds.degree16_half_14) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_16_00 : AdmissibleExponent 16 32 (102370923709/5000000000 : ℝ) := by
  have h := endpoint_admissible (s := 14) (by norm_num : 0 < (16 : ℕ))
    (half_15_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_17_00 : AdmissibleExponent 16 34 (44389096391/2000000000 : ℝ) := by
  have h := endpoint_admissible (s := 15) (by norm_num : 0 < (16 : ℕ))
    (half_16_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_18_00 : AdmissibleExponent 16 36 (239323889333/10000000000 : ℝ) := by
  have h := endpoint_admissible (s := 16) (by norm_num : 0 < (16 : ℕ))
    (half_17_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_19_00 : AdmissibleExponent 16 38 (205492917/8000000 : ℝ) := by
  have h := endpoint_admissible (s := 17) (by norm_num : 0 < (16 : ℕ))
    (half_18_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_20_00 : AdmissibleExponent 16 40 (27456201211/1000000000 : ℝ) := by
  have h := endpoint_admissible (s := 18) (by norm_num : 0 < (16 : ℕ))
    (half_19_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_21_00 : AdmissibleExponent 16 42 (146200943177/5000000000 : ℝ) := by
  have h := endpoint_admissible (s := 19) (by norm_num : 0 < (16 : ℕ))
    (half_20_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_22_00 : AdmissibleExponent 16 44 (310376768457/10000000000 : ℝ) := by
  have h := endpoint_admissible (s := 20) (by norm_num : 0 < (16 : ℕ))
    (half_21_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_23_00 : AdmissibleExponent 16 46 (328478220429/10000000000 : ℝ) := by
  have h := endpoint_admissible (s := 21) (by norm_num : 0 < (16 : ℕ))
    (half_22_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_24_00 : AdmissibleExponent 16 48 (346698331653/10000000000 : ℝ) := by
  have h := endpoint_admissible (s := 22) (by norm_num : 0 < (16 : ℕ))
    (half_23_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_25_00 : AdmissibleExponent 16 50 (14601187437/400000000 : ℝ) := by
  have h := endpoint_admissible (s := 23) (by norm_num : 0 < (16 : ℕ))
    (half_24_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_26_00 : AdmissibleExponent 16 52 (76693066111/2000000000 : ℝ) := by
  have h := endpoint_admissible (s := 24) (by norm_num : 0 < (16 : ℕ))
    (half_25_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_27_00 : AdmissibleExponent 16 54 (100499686849/2500000000 : ℝ) := by
  have h := endpoint_admissible (s := 25) (by norm_num : 0 < (16 : ℕ))
    (half_26_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_28_00 : AdmissibleExponent 16 56 (105155956421/2500000000 : ℝ) := by
  have h := endpoint_admissible (s := 26) (by norm_num : 0 < (16 : ℕ))
    (half_27_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_29_00 : AdmissibleExponent 16 58 (439334836579/10000000000 : ℝ) := by
  have h := endpoint_admissible (s := 27) (by norm_num : 0 < (16 : ℕ))
    (half_28_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_30_00 : AdmissibleExponent 16 60 (458126409293/10000000000 : ℝ) := by
  have h := endpoint_admissible (s := 28) (by norm_num : 0 < (16 : ℕ))
    (half_29_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_15_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (16307643/312500000 : ℝ)

private theorem half_15_01_total1 : total half_15_01_φ1=(16307643/312500000 : ℝ) := by
  norm_num [half_15_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_15_01_bounds1 : ∀ l,0≤half_15_01_φ1 l ∧ half_15_01_φ1 l≤1 ∧
    0≤shiftExponents 16 half_15_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (16307643/312500000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_15_01_φ2 : Fin 2 → ℝ := Fin.snoc half_15_01_φ1 (229766099/5000000000 : ℝ)

private theorem half_15_01_total2 : total half_15_01_φ2=(490688387/5000000000 : ℝ) := by
  change total (Fin.snoc half_15_01_φ1 (229766099/5000000000 : ℝ))=(490688387/5000000000 : ℝ)
  rw [alternate_total_snoc,half_15_01_total1]
  norm_num

private theorem half_15_01_bounds2 : ∀ l,0≤half_15_01_φ2 l ∧ half_15_01_φ2 l≤1 ∧
    0≤shiftExponents 16 half_15_01_φ2 l :=
  alternate_bounds_snoc half_15_01_φ1 (229766099/5000000000 : ℝ) half_15_01_bounds1 (by norm_num)

private def half_15_01_φ3 : Fin 3 → ℝ := Fin.snoc half_15_01_φ2 (222359387/5000000000 : ℝ)

private theorem half_15_01_total3 : total half_15_01_φ3=(356523887/2500000000 : ℝ) := by
  change total (Fin.snoc half_15_01_φ2 (222359387/5000000000 : ℝ))=(356523887/2500000000 : ℝ)
  rw [alternate_total_snoc,half_15_01_total2]
  norm_num

private theorem half_15_01_bounds3 : ∀ l,0≤half_15_01_φ3 l ∧ half_15_01_φ3 l≤1 ∧
    0≤shiftExponents 16 half_15_01_φ3 l :=
  alternate_bounds_snoc half_15_01_φ2 (222359387/5000000000 : ℝ) half_15_01_bounds2 (by norm_num)

private def half_15_01_φ4 : Fin 4 → ℝ := Fin.snoc half_15_01_φ3 (422339011/10000000000 : ℝ)

private theorem half_15_01_total4 : total half_15_01_φ4=(1848434559/10000000000 : ℝ) := by
  change total (Fin.snoc half_15_01_φ3 (422339011/10000000000 : ℝ))=(1848434559/10000000000 : ℝ)
  rw [alternate_total_snoc,half_15_01_total3]
  norm_num

private theorem half_15_01_bounds4 : ∀ l,0≤half_15_01_φ4 l ∧ half_15_01_φ4 l≤1 ∧
    0≤shiftExponents 16 half_15_01_φ4 l :=
  alternate_bounds_snoc half_15_01_φ3 (422339011/10000000000 : ℝ) half_15_01_bounds3 (by norm_num)

private def half_15_01_φ5 : Fin 5 → ℝ := Fin.snoc half_15_01_φ4 (186470199/5000000000 : ℝ)

private theorem half_15_01_total5 : total half_15_01_φ5=(2221374957/10000000000 : ℝ) := by
  change total (Fin.snoc half_15_01_φ4 (186470199/5000000000 : ℝ))=(2221374957/10000000000 : ℝ)
  rw [alternate_total_snoc,half_15_01_total4]
  norm_num

private theorem half_15_01_bounds5 : ∀ l,0≤half_15_01_φ5 l ∧ half_15_01_φ5 l≤1 ∧
    0≤shiftExponents 16 half_15_01_φ5 l :=
  alternate_bounds_snoc half_15_01_φ4 (186470199/5000000000 : ℝ) half_15_01_bounds4 (by norm_num)

private def half_15_01_φ6 : Fin 6 → ℝ := Fin.snoc half_15_01_φ5 (40934631/2000000000 : ℝ)

private theorem half_15_01_total6 : total half_15_01_φ6=(151628007/625000000 : ℝ) := by
  change total (Fin.snoc half_15_01_φ5 (40934631/2000000000 : ℝ))=(151628007/625000000 : ℝ)
  rw [alternate_total_snoc,half_15_01_total5]
  norm_num

private theorem half_15_01_bounds6 : ∀ l,0≤half_15_01_φ6 l ∧ half_15_01_φ6 l≤1 ∧
    0≤shiftExponents 16 half_15_01_φ6 l :=
  alternate_bounds_snoc half_15_01_φ5 (40934631/2000000000 : ℝ) half_15_01_bounds5 (by norm_num)

private theorem half_15_01_prefix : PrefixCondition 16 half_15_01_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, half_15_01_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_15_01_hF2 : SourcePowerBound
    (paddedMoment 16 0 2 64 half_15_01_φ6) (1135347937/125000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 16) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_15_01_φ6
    (fun i => (half_15_01_bounds6 i).1) (fun i => (half_15_01_bounds6 i).2.1)
    (fun i => (half_15_01_bounds6 i).2.2) half_15_01_prefix
  convert h using 1 <;> norm_num [half_15_01_total1, half_15_01_total2, half_15_01_total3, half_15_01_total4, half_15_01_total5, half_15_01_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_15_01_hF1 : SourcePowerBound
    (paddedMoment 16 0 1 64 half_15_01_φ6) (420115979/125000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 16) (j := 6) (r := 0) (n := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_15_01_φ6
    (fun i => (half_15_01_bounds6 i).1) (fun i => (half_15_01_bounds6 i).2.1)
    (fun i => (half_15_01_bounds6 i).2.2) half_15_01_prefix
  convert h using 1 <;> norm_num [half_15_01_total1, half_15_01_total2, half_15_01_total3, half_15_01_total4, half_15_01_total5, half_15_01_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_15_01_hx6 : SourcePowerBound
    (powerBoxCross 16 9 64 half_15_01_φ6) (10320612177/1000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 9) (r := 1) (v := 2) (t := 13) (D := 64)
    (a := (3/26 : ℝ)) (b := (5/26 : ℝ)) (c := (9/13 : ℝ))
    (by norm_num) half_15_01_φ6 (by norm_num [half_15_01_total1, half_15_01_total2, half_15_01_total3, half_15_01_total4, half_15_01_total5, half_15_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_15_01_total1, half_15_01_total2, half_15_01_total3, half_15_01_total4, half_15_01_total5, half_15_01_total6, parameterExponent, curveLoss, dyadicExponent]) half_15_01_hF1 half_15_01_hF2
    (SeedCompletionHigher16SimpleSeeds.degree16_half_13)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_01_total1, half_15_01_total2, half_15_01_total3, half_15_01_total4, half_15_01_total5, half_15_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_01_hx5 : SourcePowerBound
    (powerBoxCross 16 10 32 half_15_01_φ5) (22267604629/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 5) (s := 10) (u := 8) (t := 11)
    (D := 32) (ψ := (40934631/2000000000 : ℝ)) half_15_01_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_01_bounds5 l).1) (fun l => (half_15_01_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_01_total1, half_15_01_total2, half_15_01_total3, half_15_01_total4, half_15_01_total5, half_15_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_9) (SeedCompletionHigher16SimpleSeeds.degree16_half_11)
    (by simpa only [half_15_01_φ6, show (2:ℝ)*32=64 by norm_num] using half_15_01_hx6)
  exact h.weaken (by norm_num [half_15_01_total1, half_15_01_total2, half_15_01_total3, half_15_01_total4, half_15_01_total5, half_15_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_01_hx4 : SourcePowerBound
    (powerBoxCross 16 11 16 half_15_01_φ4) (123103408181/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (186470199/5000000000 : ℝ)) half_15_01_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_01_bounds4 l).1) (fun l => (half_15_01_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_01_total1, half_15_01_total2, half_15_01_total3, half_15_01_total4, half_15_01_total5, half_15_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_10) (SeedCompletionHigher16SimpleSeeds.degree16_half_12)
    (by simpa only [half_15_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_01_hx5)
  exact h.weaken (by norm_num [half_15_01_total1, half_15_01_total2, half_15_01_total3, half_15_01_total4, half_15_01_total5, half_15_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_01_hx3 : SourcePowerBound
    (powerBoxCross 16 12 8 half_15_01_φ3) (34304536571/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (422339011/10000000000 : ℝ)) half_15_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_01_bounds3 l).1) (fun l => (half_15_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_01_total1, half_15_01_total2, half_15_01_total3, half_15_01_total4, half_15_01_total5, half_15_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_11) (SeedCompletionHigher16SimpleSeeds.degree16_half_13)
    (by simpa only [half_15_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_01_hx4)
  exact h.weaken (by norm_num [half_15_01_total1, half_15_01_total2, half_15_01_total3, half_15_01_total4, half_15_01_total5, half_15_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_01_hx2 : SourcePowerBound
    (powerBoxCross 16 13 4 half_15_01_φ2) (153429980429/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (222359387/5000000000 : ℝ)) half_15_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_01_bounds2 l).1) (fun l => (half_15_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_01_total1, half_15_01_total2, half_15_01_total3, half_15_01_total4, half_15_01_total5, half_15_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_12) (SeedCompletionHigher16SimpleSeeds.degree16_half_14)
    (by simpa only [half_15_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_01_hx3)
  exact h.weaken (by norm_num [half_15_01_total1, half_15_01_total2, half_15_01_total3, half_15_01_total4, half_15_01_total5, half_15_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_01_hx1 : SourcePowerBound
    (powerBoxCross 16 14 2 half_15_01_φ1) (86254736403/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (229766099/5000000000 : ℝ)) half_15_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_01_bounds1 l).1) (fun l => (half_15_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_01_total1, half_15_01_total2, half_15_01_total3, half_15_01_total4, half_15_01_total5, half_15_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_13) (half_15_00)
    (by simpa only [half_15_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_01_hx2)
  exact h.weaken (by norm_num [half_15_01_total1, half_15_01_total2, half_15_01_total3, half_15_01_total4, half_15_01_total5, half_15_01_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_15_01 : AdmissibleExponent 16 30 (93299638179/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 13) (ψ := (16307643/312500000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (SeedCompletionHigher16SimpleSeeds.degree16_half_14)
    (by simpa only [half_15_01_φ1] using half_15_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_01_total1, half_15_01_total2, half_15_01_total3, half_15_01_total4, half_15_01_total5, half_15_01_total6, parameterExponent, curveLoss, dyadicExponent])

theorem chord_1 : AdmissibleExponent 16 32 (204165993831/10000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 32) (t := (3/4 : ℝ))
    (half_15_01) (half_19_00)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_16_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (266855849/5000000000 : ℝ)

private theorem half_16_01_total1 : total half_16_01_φ1=(266855849/5000000000 : ℝ) := by
  norm_num [half_16_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_16_01_bounds1 : ∀ l,0≤half_16_01_φ1 l ∧ half_16_01_φ1 l≤1 ∧
    0≤shiftExponents 16 half_16_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (266855849/5000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_16_01_φ2 : Fin 2 → ℝ := Fin.snoc half_16_01_φ1 (121571071/2500000000 : ℝ)

private theorem half_16_01_total2 : total half_16_01_φ2=(509997991/5000000000 : ℝ) := by
  change total (Fin.snoc half_16_01_φ1 (121571071/2500000000 : ℝ))=(509997991/5000000000 : ℝ)
  rw [alternate_total_snoc,half_16_01_total1]
  norm_num

private theorem half_16_01_bounds2 : ∀ l,0≤half_16_01_φ2 l ∧ half_16_01_φ2 l≤1 ∧
    0≤shiftExponents 16 half_16_01_φ2 l :=
  alternate_bounds_snoc half_16_01_φ1 (121571071/2500000000 : ℝ) half_16_01_bounds1 (by norm_num)

private def half_16_01_φ3 : Fin 3 → ℝ := Fin.snoc half_16_01_φ2 (457013799/10000000000 : ℝ)

private theorem half_16_01_total3 : total half_16_01_φ3=(1477009781/10000000000 : ℝ) := by
  change total (Fin.snoc half_16_01_φ2 (457013799/10000000000 : ℝ))=(1477009781/10000000000 : ℝ)
  rw [alternate_total_snoc,half_16_01_total2]
  norm_num

private theorem half_16_01_bounds3 : ∀ l,0≤half_16_01_φ3 l ∧ half_16_01_φ3 l≤1 ∧
    0≤shiftExponents 16 half_16_01_φ3 l :=
  alternate_bounds_snoc half_16_01_φ2 (457013799/10000000000 : ℝ) half_16_01_bounds2 (by norm_num)

private def half_16_01_φ4 : Fin 4 → ℝ := Fin.snoc half_16_01_φ3 (438385117/10000000000 : ℝ)

private theorem half_16_01_total4 : total half_16_01_φ4=(957697449/5000000000 : ℝ) := by
  change total (Fin.snoc half_16_01_φ3 (438385117/10000000000 : ℝ))=(957697449/5000000000 : ℝ)
  rw [alternate_total_snoc,half_16_01_total3]
  norm_num

private theorem half_16_01_bounds4 : ∀ l,0≤half_16_01_φ4 l ∧ half_16_01_φ4 l≤1 ∧
    0≤shiftExponents 16 half_16_01_φ4 l :=
  alternate_bounds_snoc half_16_01_φ3 (438385117/10000000000 : ℝ) half_16_01_bounds3 (by norm_num)

private def half_16_01_φ5 : Fin 5 → ℝ := Fin.snoc half_16_01_φ4 (100609243/2500000000 : ℝ)

private theorem half_16_01_total5 : total half_16_01_φ5=(231783187/1000000000 : ℝ) := by
  change total (Fin.snoc half_16_01_φ4 (100609243/2500000000 : ℝ))=(231783187/1000000000 : ℝ)
  rw [alternate_total_snoc,half_16_01_total4]
  norm_num

private theorem half_16_01_bounds5 : ∀ l,0≤half_16_01_φ5 l ∧ half_16_01_φ5 l≤1 ∧
    0≤shiftExponents 16 half_16_01_φ5 l :=
  alternate_bounds_snoc half_16_01_φ4 (100609243/2500000000 : ℝ) half_16_01_bounds4 (by norm_num)

private def half_16_01_φ6 : Fin 6 → ℝ := Fin.snoc half_16_01_φ5 (300934121/10000000000 : ℝ)

private theorem half_16_01_total6 : total half_16_01_φ6=(2618765991/10000000000 : ℝ) := by
  change total (Fin.snoc half_16_01_φ5 (300934121/10000000000 : ℝ))=(2618765991/10000000000 : ℝ)
  rw [alternate_total_snoc,half_16_01_total5]
  norm_num

private theorem half_16_01_bounds6 : ∀ l,0≤half_16_01_φ6 l ∧ half_16_01_φ6 l≤1 ∧
    0≤shiftExponents 16 half_16_01_φ6 l :=
  alternate_bounds_snoc half_16_01_φ5 (300934121/10000000000 : ℝ) half_16_01_bounds5 (by norm_num)

private theorem half_16_01_prefix : PrefixCondition 16 half_16_01_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, half_16_01_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_16_01_hF2 : SourcePowerBound
    (paddedMoment 16 0 2 64 half_16_01_φ6) (16431106081/2000000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 16) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_16_01_φ6
    (fun i => (half_16_01_bounds6 i).1) (fun i => (half_16_01_bounds6 i).2.1)
    (fun i => (half_16_01_bounds6 i).2.2) half_16_01_prefix
  convert h using 1 <;> norm_num [half_16_01_total1, half_16_01_total2, half_16_01_total3, half_16_01_total4, half_16_01_total5, half_16_01_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_16_01_hx6 : SourcePowerBound
    (powerBoxCross 16 10 64 half_16_01_φ6) (21938803801/2000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 10) (r := 2) (v := 13) (w := 14) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_16_01_φ6 (by norm_num [half_16_01_total1, half_16_01_total2, half_16_01_total3, half_16_01_total4, half_16_01_total5, half_16_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_16_01_total1, half_16_01_total2, half_16_01_total3, half_16_01_total4, half_16_01_total5, half_16_01_total6, parameterExponent, curveLoss, dyadicExponent]) half_16_01_hF2
    (SeedCompletionHigher16SimpleSeeds.degree16_half_13) (SeedCompletionHigher16SimpleSeeds.degree16_half_14)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_01_total1, half_16_01_total2, half_16_01_total3, half_16_01_total4, half_16_01_total5, half_16_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_01_hx5 : SourcePowerBound
    (powerBoxCross 16 11 32 half_16_01_φ5) (119751135979/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 5) (s := 11) (u := 9) (t := 12)
    (D := 32) (ψ := (300934121/10000000000 : ℝ)) half_16_01_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_01_bounds5 l).1) (fun l => (half_16_01_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_01_total1, half_16_01_total2, half_16_01_total3, half_16_01_total4, half_16_01_total5, half_16_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_10) (SeedCompletionHigher16SimpleSeeds.degree16_half_12)
    (by simpa only [half_16_01_φ6, show (2:ℝ)*32=64 by norm_num] using half_16_01_hx6)
  exact h.weaken (by norm_num [half_16_01_total1, half_16_01_total2, half_16_01_total3, half_16_01_total4, half_16_01_total5, half_16_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_01_hx4 : SourcePowerBound
    (powerBoxCross 16 12 16 half_16_01_φ4) (8302739999/625000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (100609243/2500000000 : ℝ)) half_16_01_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_01_bounds4 l).1) (fun l => (half_16_01_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_01_total1, half_16_01_total2, half_16_01_total3, half_16_01_total4, half_16_01_total5, half_16_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_11) (SeedCompletionHigher16SimpleSeeds.degree16_half_13)
    (by simpa only [half_16_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_01_hx5)
  exact h.weaken (by norm_num [half_16_01_total1, half_16_01_total2, half_16_01_total3, half_16_01_total4, half_16_01_total5, half_16_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_01_hx3 : SourcePowerBound
    (powerBoxCross 16 13 8 half_16_01_φ3) (29643480601/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (438385117/10000000000 : ℝ)) half_16_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_01_bounds3 l).1) (fun l => (half_16_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_01_total1, half_16_01_total2, half_16_01_total3, half_16_01_total4, half_16_01_total5, half_16_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_12) (SeedCompletionHigher16SimpleSeeds.degree16_half_14)
    (by simpa only [half_16_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_01_hx4)
  exact h.weaken (by norm_num [half_16_01_total1, half_16_01_total2, half_16_01_total3, half_16_01_total4, half_16_01_total5, half_16_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_01_hx2 : SourcePowerBound
    (powerBoxCross 16 14 4 half_16_01_φ2) (82977258349/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (457013799/10000000000 : ℝ)) half_16_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_01_bounds2 l).1) (fun l => (half_16_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_01_total1, half_16_01_total2, half_16_01_total3, half_16_01_total4, half_16_01_total5, half_16_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_13) (half_15_01)
    (by simpa only [half_16_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_01_hx3)
  exact h.weaken (by norm_num [half_16_01_total1, half_16_01_total2, half_16_01_total3, half_16_01_total4, half_16_01_total5, half_16_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_01_hx1 : SourcePowerBound
    (powerBoxCross 16 15 2 half_16_01_φ1) (93586983201/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (121571071/2500000000 : ℝ)) half_16_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_01_bounds1 l).1) (fun l => (half_16_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_01_total1, half_16_01_total2, half_16_01_total3, half_16_01_total4, half_16_01_total5, half_16_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_14) (chord_1)
    (by simpa only [half_16_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_01_hx2)
  exact h.weaken (by norm_num [half_16_01_total1, half_16_01_total2, half_16_01_total3, half_16_01_total4, half_16_01_total5, half_16_01_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_16_01 : AdmissibleExponent 16 32 (50662901411/2500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 14) (ψ := (266855849/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_15_01)
    (by simpa only [half_16_01_φ1] using half_16_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_01_total1, half_16_01_total2, half_16_01_total3, half_16_01_total4, half_16_01_total5, half_16_01_total6, parameterExponent, curveLoss, dyadicExponent])

theorem chord_4 : AdmissibleExponent 16 34 (110300830893/5000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 34) (t := (4/5 : ℝ))
    (half_16_01) (half_21_00)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_17_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (541378237/10000000000 : ℝ)

private theorem half_17_01_total1 : total half_17_01_φ1=(541378237/10000000000 : ℝ) := by
  norm_num [half_17_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_17_01_bounds1 : ∀ l,0≤half_17_01_φ1 l ∧ half_17_01_φ1 l≤1 ∧
    0≤shiftExponents 16 half_17_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (541378237/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_17_01_φ2 : Fin 2 → ℝ := Fin.snoc half_17_01_φ1 (243786607/5000000000 : ℝ)

private theorem half_17_01_total2 : total half_17_01_φ2=(1028951451/10000000000 : ℝ) := by
  change total (Fin.snoc half_17_01_φ1 (243786607/5000000000 : ℝ))=(1028951451/10000000000 : ℝ)
  rw [alternate_total_snoc,half_17_01_total1]
  norm_num

private theorem half_17_01_bounds2 : ∀ l,0≤half_17_01_φ2 l ∧ half_17_01_φ2 l≤1 ∧
    0≤shiftExponents 16 half_17_01_φ2 l :=
  alternate_bounds_snoc half_17_01_φ1 (243786607/5000000000 : ℝ) half_17_01_bounds1 (by norm_num)

private def half_17_01_φ3 : Fin 3 → ℝ := Fin.snoc half_17_01_φ2 (120996511/2500000000 : ℝ)

private theorem half_17_01_total3 : total half_17_01_φ3=(302587499/2000000000 : ℝ) := by
  change total (Fin.snoc half_17_01_φ2 (120996511/2500000000 : ℝ))=(302587499/2000000000 : ℝ)
  rw [alternate_total_snoc,half_17_01_total2]
  norm_num

private theorem half_17_01_bounds3 : ∀ l,0≤half_17_01_φ3 l ∧ half_17_01_φ3 l≤1 ∧
    0≤shiftExponents 16 half_17_01_φ3 l :=
  alternate_bounds_snoc half_17_01_φ2 (120996511/2500000000 : ℝ) half_17_01_bounds2 (by norm_num)

private def half_17_01_φ4 : Fin 4 → ℝ := Fin.snoc half_17_01_φ3 (454233471/10000000000 : ℝ)

private theorem half_17_01_total4 : total half_17_01_φ4=(983585483/5000000000 : ℝ) := by
  change total (Fin.snoc half_17_01_φ3 (454233471/10000000000 : ℝ))=(983585483/5000000000 : ℝ)
  rw [alternate_total_snoc,half_17_01_total3]
  norm_num

private theorem half_17_01_bounds4 : ∀ l,0≤half_17_01_φ4 l ∧ half_17_01_φ4 l≤1 ∧
    0≤shiftExponents 16 half_17_01_φ4 l :=
  alternate_bounds_snoc half_17_01_φ3 (454233471/10000000000 : ℝ) half_17_01_bounds3 (by norm_num)

private def half_17_01_φ5 : Fin 5 → ℝ := Fin.snoc half_17_01_φ4 (86235637/2000000000 : ℝ)

private theorem half_17_01_total5 : total half_17_01_φ5=(2398349151/10000000000 : ℝ) := by
  change total (Fin.snoc half_17_01_φ4 (86235637/2000000000 : ℝ))=(2398349151/10000000000 : ℝ)
  rw [alternate_total_snoc,half_17_01_total4]
  norm_num

private theorem half_17_01_bounds5 : ∀ l,0≤half_17_01_φ5 l ∧ half_17_01_φ5 l≤1 ∧
    0≤shiftExponents 16 half_17_01_φ5 l :=
  alternate_bounds_snoc half_17_01_φ4 (86235637/2000000000 : ℝ) half_17_01_bounds4 (by norm_num)

private def half_17_01_φ6 : Fin 6 → ℝ := Fin.snoc half_17_01_φ5 (94870417/2500000000 : ℝ)

private theorem half_17_01_total6 : total half_17_01_φ6=(2777830819/10000000000 : ℝ) := by
  change total (Fin.snoc half_17_01_φ5 (94870417/2500000000 : ℝ))=(2777830819/10000000000 : ℝ)
  rw [alternate_total_snoc,half_17_01_total5]
  norm_num

private theorem half_17_01_bounds6 : ∀ l,0≤half_17_01_φ6 l ∧ half_17_01_φ6 l≤1 ∧
    0≤shiftExponents 16 half_17_01_φ6 l :=
  alternate_bounds_snoc half_17_01_φ5 (94870417/2500000000 : ℝ) half_17_01_bounds5 (by norm_num)

private def half_17_01_φ7 : Fin 7 → ℝ := Fin.snoc half_17_01_φ6 (217522923/10000000000 : ℝ)

private theorem half_17_01_total7 : total half_17_01_φ7=(1497676871/5000000000 : ℝ) := by
  change total (Fin.snoc half_17_01_φ6 (217522923/10000000000 : ℝ))=(1497676871/5000000000 : ℝ)
  rw [alternate_total_snoc,half_17_01_total6]
  norm_num

private theorem half_17_01_bounds7 : ∀ l,0≤half_17_01_φ7 l ∧ half_17_01_φ7 l≤1 ∧
    0≤shiftExponents 16 half_17_01_φ7 l :=
  alternate_bounds_snoc half_17_01_φ6 (217522923/10000000000 : ℝ) half_17_01_bounds6 (by norm_num)

private theorem half_17_01_prefix : PrefixCondition 16 half_17_01_φ7 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, half_17_01_φ6, half_17_01_φ7, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_17_01_hF2 : SourcePowerBound
    (paddedMoment 16 0 2 128 half_17_01_φ7) (9520908161/1000000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 16) (j := 7) (r := 0) (n := 1) (D := 128)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_17_01_φ7
    (fun i => (half_17_01_bounds7 i).1) (fun i => (half_17_01_bounds7 i).2.1)
    (fun i => (half_17_01_bounds7 i).2.2) half_17_01_prefix
  convert h using 1 <;> norm_num [half_17_01_total1, half_17_01_total2, half_17_01_total3, half_17_01_total4, half_17_01_total5, half_17_01_total6, half_17_01_total7, parameterExponent, curveLoss, dyadicExponent]

private theorem half_17_01_hF1 : SourcePowerBound
    (paddedMoment 16 0 1 128 half_17_01_φ7) (3506969387/1000000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 16) (j := 7) (r := 0) (n := 0) (D := 128)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_17_01_φ7
    (fun i => (half_17_01_bounds7 i).1) (fun i => (half_17_01_bounds7 i).2.1)
    (fun i => (half_17_01_bounds7 i).2.2) half_17_01_prefix
  convert h using 1 <;> norm_num [half_17_01_total1, half_17_01_total2, half_17_01_total3, half_17_01_total4, half_17_01_total5, half_17_01_total6, half_17_01_total7, parameterExponent, curveLoss, dyadicExponent]

private theorem half_17_01_hx7 : SourcePowerBound
    (powerBoxCross 16 10 128 half_17_01_φ7) (27104195919/2500000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 10) (r := 1) (v := 2) (t := 14) (D := 128)
    (a := (1/14 : ℝ)) (b := (3/14 : ℝ)) (c := (5/7 : ℝ))
    (by norm_num) half_17_01_φ7 (by norm_num [half_17_01_total1, half_17_01_total2, half_17_01_total3, half_17_01_total4, half_17_01_total5, half_17_01_total6, half_17_01_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_17_01_total1, half_17_01_total2, half_17_01_total3, half_17_01_total4, half_17_01_total5, half_17_01_total6, half_17_01_total7, parameterExponent, curveLoss, dyadicExponent]) half_17_01_hF1 half_17_01_hF2
    (SeedCompletionHigher16SimpleSeeds.degree16_half_14)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_01_total1, half_17_01_total2, half_17_01_total3, half_17_01_total4, half_17_01_total5, half_17_01_total6, half_17_01_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_01_hx6 : SourcePowerBound
    (powerBoxCross 16 11 64 half_17_01_φ6) (116610977551/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 6) (s := 11) (u := 9) (t := 12)
    (D := 64) (ψ := (217522923/10000000000 : ℝ)) half_17_01_φ6
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_01_bounds6 l).1) (fun l => (half_17_01_bounds6 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_01_total1, half_17_01_total2, half_17_01_total3, half_17_01_total4, half_17_01_total5, half_17_01_total6, half_17_01_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_10) (SeedCompletionHigher16SimpleSeeds.degree16_half_12)
    (by simpa only [half_17_01_φ7, show (2:ℝ)*64=128 by norm_num] using half_17_01_hx7)
  exact h.weaken (by norm_num [half_17_01_total1, half_17_01_total2, half_17_01_total3, half_17_01_total4, half_17_01_total5, half_17_01_total6, half_17_01_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_01_hx5 : SourcePowerBound
    (powerBoxCross 16 12 32 half_17_01_φ5) (128640649121/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 5) (s := 12) (u := 10) (t := 13)
    (D := 32) (ψ := (94870417/2500000000 : ℝ)) half_17_01_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_01_bounds5 l).1) (fun l => (half_17_01_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_01_total1, half_17_01_total2, half_17_01_total3, half_17_01_total4, half_17_01_total5, half_17_01_total6, half_17_01_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_11) (SeedCompletionHigher16SimpleSeeds.degree16_half_13)
    (by simpa only [half_17_01_φ6, show (2:ℝ)*32=64 by norm_num] using half_17_01_hx6)
  exact h.weaken (by norm_num [half_17_01_total1, half_17_01_total2, half_17_01_total3, half_17_01_total4, half_17_01_total5, half_17_01_total6, half_17_01_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_01_hx4 : SourcePowerBound
    (powerBoxCross 16 13 16 half_17_01_φ4) (71584068869/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (86235637/2000000000 : ℝ)) half_17_01_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_01_bounds4 l).1) (fun l => (half_17_01_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_01_total1, half_17_01_total2, half_17_01_total3, half_17_01_total4, half_17_01_total5, half_17_01_total6, half_17_01_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_12) (SeedCompletionHigher16SimpleSeeds.degree16_half_14)
    (by simpa only [half_17_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_01_hx5)
  exact h.weaken (by norm_num [half_17_01_total1, half_17_01_total2, half_17_01_total3, half_17_01_total4, half_17_01_total5, half_17_01_total6, half_17_01_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_01_hx3 : SourcePowerBound
    (powerBoxCross 16 14 8 half_17_01_φ3) (20012367767/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (454233471/10000000000 : ℝ)) half_17_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_01_bounds3 l).1) (fun l => (half_17_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_01_total1, half_17_01_total2, half_17_01_total3, half_17_01_total4, half_17_01_total5, half_17_01_total6, half_17_01_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_13) (half_15_01)
    (by simpa only [half_17_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_01_hx4)
  exact h.weaken (by norm_num [half_17_01_total1, half_17_01_total2, half_17_01_total3, half_17_01_total4, half_17_01_total5, half_17_01_total6, half_17_01_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_01_hx2 : SourcePowerBound
    (powerBoxCross 16 15 4 half_17_01_φ2) (89883008209/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (120996511/2500000000 : ℝ)) half_17_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_01_bounds2 l).1) (fun l => (half_17_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_01_total1, half_17_01_total2, half_17_01_total3, half_17_01_total4, half_17_01_total5, half_17_01_total6, half_17_01_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_14) (half_16_01)
    (by simpa only [half_17_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_01_hx3)
  exact h.weaken (by norm_num [half_17_01_total1, half_17_01_total2, half_17_01_total3, half_17_01_total4, half_17_01_total5, half_17_01_total6, half_17_01_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_01_hx1 : SourcePowerBound
    (powerBoxCross 16 16 2 half_17_01_φ1) (202221866991/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (243786607/5000000000 : ℝ)) half_17_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_01_bounds1 l).1) (fun l => (half_17_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_01_total1, half_17_01_total2, half_17_01_total3, half_17_01_total4, half_17_01_total5, half_17_01_total6, half_17_01_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_01) (chord_4)
    (by simpa only [half_17_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_01_hx2)
  exact h.weaken (by norm_num [half_17_01_total1, half_17_01_total2, half_17_01_total3, half_17_01_total4, half_17_01_total5, half_17_01_total6, half_17_01_total7, parameterExponent, curveLoss, dyadicExponent])

theorem half_17_01 : AdmissibleExponent 16 34 (109502296169/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 15) (ψ := (541378237/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_16_01)
    (by simpa only [half_17_01_φ1] using half_17_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_01_total1, half_17_01_total2, half_17_01_total3, half_17_01_total4, half_17_01_total5, half_17_01_total6, half_17_01_total7, parameterExponent, curveLoss, dyadicExponent])

theorem chord_8 : AdmissibleExponent 16 36 (1660725885681/70000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 36) (t := (6/7 : ℝ))
    (half_17_01) (half_24_00)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_18_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (549118031/10000000000 : ℝ)

private theorem half_18_01_total1 : total half_18_01_φ1=(549118031/10000000000 : ℝ) := by
  norm_num [half_18_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_18_01_bounds1 : ∀ l,0≤half_18_01_φ1 l ∧ half_18_01_φ1 l≤1 ∧
    0≤shiftExponents 16 half_18_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (549118031/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_18_01_φ2 : Fin 2 → ℝ := Fin.snoc half_18_01_φ1 (98621341/2000000000 : ℝ)

private theorem half_18_01_total2 : total half_18_01_φ2=(32569523/312500000 : ℝ) := by
  change total (Fin.snoc half_18_01_φ1 (98621341/2000000000 : ℝ))=(32569523/312500000 : ℝ)
  rw [alternate_total_snoc,half_18_01_total1]
  norm_num

private theorem half_18_01_bounds2 : ∀ l,0≤half_18_01_φ2 l ∧ half_18_01_φ2 l≤1 ∧
    0≤shiftExponents 16 half_18_01_φ2 l :=
  alternate_bounds_snoc half_18_01_φ1 (98621341/2000000000 : ℝ) half_18_01_bounds1 (by norm_num)

private def half_18_01_φ3 : Fin 3 → ℝ := Fin.snoc half_18_01_φ2 (485895703/10000000000 : ℝ)

private theorem half_18_01_total3 : total half_18_01_φ3=(1528120439/10000000000 : ℝ) := by
  change total (Fin.snoc half_18_01_φ2 (485895703/10000000000 : ℝ))=(1528120439/10000000000 : ℝ)
  rw [alternate_total_snoc,half_18_01_total2]
  norm_num

private theorem half_18_01_bounds3 : ∀ l,0≤half_18_01_φ3 l ∧ half_18_01_φ3 l≤1 ∧
    0≤shiftExponents 16 half_18_01_φ3 l :=
  alternate_bounds_snoc half_18_01_φ2 (485895703/10000000000 : ℝ) half_18_01_bounds2 (by norm_num)

private def half_18_01_φ4 : Fin 4 → ℝ := Fin.snoc half_18_01_φ3 (480709631/10000000000 : ℝ)

private theorem half_18_01_total4 : total half_18_01_φ4=(200883007/1000000000 : ℝ) := by
  change total (Fin.snoc half_18_01_φ3 (480709631/10000000000 : ℝ))=(200883007/1000000000 : ℝ)
  rw [alternate_total_snoc,half_18_01_total3]
  norm_num

private theorem half_18_01_bounds4 : ∀ l,0≤half_18_01_φ4 l ∧ half_18_01_φ4 l≤1 ∧
    0≤shiftExponents 16 half_18_01_φ4 l :=
  alternate_bounds_snoc half_18_01_φ3 (480709631/10000000000 : ℝ) half_18_01_bounds3 (by norm_num)

private def half_18_01_φ5 : Fin 5 → ℝ := Fin.snoc half_18_01_φ4 (224232833/5000000000 : ℝ)

private theorem half_18_01_total5 : total half_18_01_φ5=(307161967/1250000000 : ℝ) := by
  change total (Fin.snoc half_18_01_φ4 (224232833/5000000000 : ℝ))=(307161967/1250000000 : ℝ)
  rw [alternate_total_snoc,half_18_01_total4]
  norm_num

private theorem half_18_01_bounds5 : ∀ l,0≤half_18_01_φ5 l ∧ half_18_01_φ5 l≤1 ∧
    0≤shiftExponents 16 half_18_01_φ5 l :=
  alternate_bounds_snoc half_18_01_φ4 (224232833/5000000000 : ℝ) half_18_01_bounds4 (by norm_num)

private def half_18_01_φ6 : Fin 6 → ℝ := Fin.snoc half_18_01_φ5 (82849129/2000000000 : ℝ)

private theorem half_18_01_total6 : total half_18_01_φ6=(2871541381/10000000000 : ℝ) := by
  change total (Fin.snoc half_18_01_φ5 (82849129/2000000000 : ℝ))=(2871541381/10000000000 : ℝ)
  rw [alternate_total_snoc,half_18_01_total5]
  norm_num

private theorem half_18_01_bounds6 : ∀ l,0≤half_18_01_φ6 l ∧ half_18_01_φ6 l≤1 ∧
    0≤shiftExponents 16 half_18_01_φ6 l :=
  alternate_bounds_snoc half_18_01_φ5 (82849129/2000000000 : ℝ) half_18_01_bounds5 (by norm_num)

private def half_18_01_φ7 : Fin 7 → ℝ := Fin.snoc half_18_01_φ6 (322777523/10000000000 : ℝ)

private theorem half_18_01_total7 : total half_18_01_φ7=(399289863/1250000000 : ℝ) := by
  change total (Fin.snoc half_18_01_φ6 (322777523/10000000000 : ℝ))=(399289863/1250000000 : ℝ)
  rw [alternate_total_snoc,half_18_01_total6]
  norm_num

private theorem half_18_01_bounds7 : ∀ l,0≤half_18_01_φ7 l ∧ half_18_01_φ7 l≤1 ∧
    0≤shiftExponents 16 half_18_01_φ7 l :=
  alternate_bounds_snoc half_18_01_φ6 (322777523/10000000000 : ℝ) half_18_01_bounds6 (by norm_num)

private theorem half_18_01_prefix : PrefixCondition 16 half_18_01_φ7 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_18_01_φ1, half_18_01_φ2, half_18_01_φ3, half_18_01_φ4, half_18_01_φ5, half_18_01_φ6, half_18_01_φ7, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_18_01_hF2 : SourcePowerBound
    (paddedMoment 16 0 2 128 half_18_01_φ7) (2156391233/250000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 16) (j := 7) (r := 0) (n := 1) (D := 128)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_18_01_φ7
    (fun i => (half_18_01_bounds7 i).1) (fun i => (half_18_01_bounds7 i).2.1)
    (fun i => (half_18_01_bounds7 i).2.2) half_18_01_prefix
  convert h using 1 <;> norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, half_18_01_total7, parameterExponent, curveLoss, dyadicExponent]

private theorem half_18_01_hx7 : SourcePowerBound
    (powerBoxCross 16 11 128 half_18_01_φ7) (114139011641/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 11) (r := 2) (v := 14) (w := 15) (D := 128)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_18_01_φ7 (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, half_18_01_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, half_18_01_total7, parameterExponent, curveLoss, dyadicExponent]) half_18_01_hF2
    (SeedCompletionHigher16SimpleSeeds.degree16_half_14) (half_15_01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, half_18_01_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_01_hx6 : SourcePowerBound
    (powerBoxCross 16 12 64 half_18_01_φ6) (15570826109/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 6) (s := 12) (u := 10) (t := 13)
    (D := 64) (ψ := (322777523/10000000000 : ℝ)) half_18_01_φ6
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_01_bounds6 l).1) (fun l => (half_18_01_bounds6 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, half_18_01_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_11) (SeedCompletionHigher16SimpleSeeds.degree16_half_13)
    (by simpa only [half_18_01_φ7, show (2:ℝ)*64=128 by norm_num] using half_18_01_hx7)
  exact h.weaken (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, half_18_01_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_01_hx5 : SourcePowerBound
    (powerBoxCross 16 13 32 half_18_01_φ5) (17259023447/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 5) (s := 13) (u := 11) (t := 14)
    (D := 32) (ψ := (82849129/2000000000 : ℝ)) half_18_01_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_01_bounds5 l).1) (fun l => (half_18_01_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, half_18_01_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_12) (SeedCompletionHigher16SimpleSeeds.degree16_half_14)
    (by simpa only [half_18_01_φ6, show (2:ℝ)*32=64 by norm_num] using half_18_01_hx6)
  exact h.weaken (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, half_18_01_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_01_hx4 : SourcePowerBound
    (powerBoxCross 16 14 16 half_18_01_φ4) (77066507699/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 14) (u := 12) (t := 15)
    (D := 16) (ψ := (224232833/5000000000 : ℝ)) half_18_01_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_01_bounds4 l).1) (fun l => (half_18_01_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, half_18_01_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_13) (half_15_01)
    (by simpa only [half_18_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_18_01_hx5)
  exact h.weaken (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, half_18_01_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_01_hx3 : SourcePowerBound
    (powerBoxCross 16 15 8 half_18_01_φ3) (86468592109/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 15) (u := 13) (t := 16)
    (D := 8) (ψ := (480709631/10000000000 : ℝ)) half_18_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_01_bounds3 l).1) (fun l => (half_18_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, half_18_01_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_14) (half_16_01)
    (by simpa only [half_18_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_18_01_hx4)
  exact h.weaken (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, half_18_01_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_01_hx2 : SourcePowerBound
    (powerBoxCross 16 16 4 half_18_01_φ2) (4844677257/250000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 16) (u := 14) (t := 17)
    (D := 4) (ψ := (485895703/10000000000 : ℝ)) half_18_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_01_bounds2 l).1) (fun l => (half_18_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, half_18_01_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_01) (half_17_01)
    (by simpa only [half_18_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_18_01_hx3)
  exact h.weaken (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, half_18_01_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_01_hx1 : SourcePowerBound
    (powerBoxCross 16 17 2 half_18_01_φ1) (54381943331/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 17) (u := 15) (t := 18)
    (D := 2) (ψ := (98621341/2000000000 : ℝ)) half_18_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_01_bounds1 l).1) (fun l => (half_18_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, half_18_01_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_01) (chord_8)
    (by simpa only [half_18_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_18_01_hx2)
  exact h.weaken (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, half_18_01_total7, parameterExponent, curveLoss, dyadicExponent])

theorem half_18_01 : AdmissibleExponent 16 36 (235648668347/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 16) (ψ := (549118031/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_17_01)
    (by simpa only [half_18_01_φ1] using half_18_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, half_18_01_total7, parameterExponent, curveLoss, dyadicExponent])

theorem chord_14 : AdmissibleExponent 16 38 (254125751123/10000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 38) (t := (7/8 : ℝ))
    (half_18_01) (half_26_00)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_19_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (69515861/1250000000 : ℝ)

private theorem half_19_01_total1 : total half_19_01_φ1=(69515861/1250000000 : ℝ) := by
  norm_num [half_19_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_19_01_bounds1 : ∀ l,0≤half_19_01_φ1 l ∧ half_19_01_φ1 l≤1 ∧
    0≤shiftExponents 16 half_19_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (69515861/1250000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_19_01_φ2 : Fin 2 → ℝ := Fin.snoc half_19_01_φ1 (12531451/250000000 : ℝ)

private theorem half_19_01_total2 : total half_19_01_φ2=(33043279/312500000 : ℝ) := by
  change total (Fin.snoc half_19_01_φ1 (12531451/250000000 : ℝ))=(33043279/312500000 : ℝ)
  rw [alternate_total_snoc,half_19_01_total1]
  norm_num

private theorem half_19_01_bounds2 : ∀ l,0≤half_19_01_φ2 l ∧ half_19_01_φ2 l≤1 ∧
    0≤shiftExponents 16 half_19_01_φ2 l :=
  alternate_bounds_snoc half_19_01_φ1 (12531451/250000000 : ℝ) half_19_01_bounds1 (by norm_num)

private def half_19_01_φ3 : Fin 3 → ℝ := Fin.snoc half_19_01_φ2 (123136481/2500000000 : ℝ)

private theorem half_19_01_total3 : total half_19_01_φ3=(387482713/2500000000 : ℝ) := by
  change total (Fin.snoc half_19_01_φ2 (123136481/2500000000 : ℝ))=(387482713/2500000000 : ℝ)
  rw [alternate_total_snoc,half_19_01_total2]
  norm_num

private theorem half_19_01_bounds3 : ∀ l,0≤half_19_01_φ3 l ∧ half_19_01_φ3 l≤1 ∧
    0≤shiftExponents 16 half_19_01_φ3 l :=
  alternate_bounds_snoc half_19_01_φ2 (123136481/2500000000 : ℝ) half_19_01_bounds2 (by norm_num)

private def half_19_01_φ4 : Fin 4 → ℝ := Fin.snoc half_19_01_φ3 (485659333/10000000000 : ℝ)

private theorem half_19_01_total4 : total half_19_01_φ4=(407118037/2000000000 : ℝ) := by
  change total (Fin.snoc half_19_01_φ3 (485659333/10000000000 : ℝ))=(407118037/2000000000 : ℝ)
  rw [alternate_total_snoc,half_19_01_total3]
  norm_num

private theorem half_19_01_bounds4 : ∀ l,0≤half_19_01_φ4 l ∧ half_19_01_φ4 l≤1 ∧
    0≤shiftExponents 16 half_19_01_φ4 l :=
  alternate_bounds_snoc half_19_01_φ3 (485659333/10000000000 : ℝ) half_19_01_bounds3 (by norm_num)

private def half_19_01_φ5 : Fin 5 → ℝ := Fin.snoc half_19_01_φ4 (240843901/5000000000 : ℝ)

private theorem half_19_01_total5 : total half_19_01_φ5=(2517277987/10000000000 : ℝ) := by
  change total (Fin.snoc half_19_01_φ4 (240843901/5000000000 : ℝ))=(2517277987/10000000000 : ℝ)
  rw [alternate_total_snoc,half_19_01_total4]
  norm_num

private theorem half_19_01_bounds5 : ∀ l,0≤half_19_01_φ5 l ∧ half_19_01_φ5 l≤1 ∧
    0≤shiftExponents 16 half_19_01_φ5 l :=
  alternate_bounds_snoc half_19_01_φ4 (240843901/5000000000 : ℝ) half_19_01_bounds4 (by norm_num)

private def half_19_01_φ6 : Fin 6 → ℝ := Fin.snoc half_19_01_φ5 (28494589/625000000 : ℝ)

private theorem half_19_01_total6 : total half_19_01_φ6=(2973191411/10000000000 : ℝ) := by
  change total (Fin.snoc half_19_01_φ5 (28494589/625000000 : ℝ))=(2973191411/10000000000 : ℝ)
  rw [alternate_total_snoc,half_19_01_total5]
  norm_num

private theorem half_19_01_bounds6 : ∀ l,0≤half_19_01_φ6 l ∧ half_19_01_φ6 l≤1 ∧
    0≤shiftExponents 16 half_19_01_φ6 l :=
  alternate_bounds_snoc half_19_01_φ5 (28494589/625000000 : ℝ) half_19_01_bounds5 (by norm_num)

private def half_19_01_φ7 : Fin 7 → ℝ := Fin.snoc half_19_01_φ6 (360141919/10000000000 : ℝ)

private theorem half_19_01_total7 : total half_19_01_φ7=(333333333/1000000000 : ℝ) := by
  change total (Fin.snoc half_19_01_φ6 (360141919/10000000000 : ℝ))=(333333333/1000000000 : ℝ)
  rw [alternate_total_snoc,half_19_01_total6]
  norm_num

private theorem half_19_01_bounds7 : ∀ l,0≤half_19_01_φ7 l ∧ half_19_01_φ7 l≤1 ∧
    0≤shiftExponents 16 half_19_01_φ7 l :=
  alternate_bounds_snoc half_19_01_φ6 (360141919/10000000000 : ℝ) half_19_01_bounds6 (by norm_num)

private theorem half_19_01_prefix : PrefixCondition 16 half_19_01_φ7 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_19_01_φ1, half_19_01_φ2, half_19_01_φ3, half_19_01_φ4, half_19_01_φ5, half_19_01_φ6, half_19_01_φ7, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_19_01_hF4 : SourcePowerBound
    (paddedMoment 16 0 4 128 half_19_01_φ7) (3800000007/200000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 16) (j := 7) (r := 0) (n := 2) (D := 128)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_19_01_φ7
    (fun i => (half_19_01_bounds7 i).1) (fun i => (half_19_01_bounds7 i).2.1)
    (fun i => (half_19_01_bounds7 i).2.2) half_19_01_prefix
  convert h using 1 <;> norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, half_19_01_total7, parameterExponent, curveLoss, dyadicExponent]

private theorem half_19_01_hF2 : SourcePowerBound
    (paddedMoment 16 0 2 128 half_19_01_φ7) (1600000003/200000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 16) (j := 7) (r := 0) (n := 1) (D := 128)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_19_01_φ7
    (fun i => (half_19_01_bounds7 i).1) (fun i => (half_19_01_bounds7 i).2.1)
    (fun i => (half_19_01_bounds7 i).2.2) half_19_01_prefix
  convert h using 1 <;> norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, half_19_01_total7, parameterExponent, curveLoss, dyadicExponent]

private theorem half_19_01_hx7 : SourcePowerBound
    (powerBoxCross 16 12 128 half_19_01_φ7) (30254903537/2500000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 12) (r := 2) (v := 4) (t := 15) (D := 128)
    (a := (3/20 : ℝ)) (b := (1/20 : ℝ)) (c := (4/5 : ℝ))
    (by norm_num) half_19_01_φ7 (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, half_19_01_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, half_19_01_total7, parameterExponent, curveLoss, dyadicExponent]) half_19_01_hF2 half_19_01_hF4
    (half_15_01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, half_19_01_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_01_hx6 : SourcePowerBound
    (powerBoxCross 16 13 64 half_19_01_φ6) (33099697319/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 6) (s := 13) (u := 11) (t := 14)
    (D := 64) (ψ := (360141919/10000000000 : ℝ)) half_19_01_φ6
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_01_bounds6 l).1) (fun l => (half_19_01_bounds6 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, half_19_01_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_12) (SeedCompletionHigher16SimpleSeeds.degree16_half_14)
    (by simpa only [half_19_01_φ7, show (2:ℝ)*64=128 by norm_num] using half_19_01_hx7)
  exact h.weaken (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, half_19_01_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_01_hx5 : SourcePowerBound
    (powerBoxCross 16 14 32 half_19_01_φ5) (147832253177/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 5) (s := 14) (u := 12) (t := 15)
    (D := 32) (ψ := (28494589/625000000 : ℝ)) half_19_01_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_01_bounds5 l).1) (fun l => (half_19_01_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, half_19_01_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_13) (half_15_01)
    (by simpa only [half_19_01_φ6, show (2:ℝ)*32=64 by norm_num] using half_19_01_hx6)
  exact h.weaken (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, half_19_01_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_01_hx4 : SourcePowerBound
    (powerBoxCross 16 15 16 half_19_01_φ4) (165852007379/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 15) (u := 13) (t := 16)
    (D := 16) (ψ := (240843901/5000000000 : ℝ)) half_19_01_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_01_bounds4 l).1) (fun l => (half_19_01_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, half_19_01_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_14) (half_16_01)
    (by simpa only [half_19_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_19_01_hx5)
  exact h.weaken (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, half_19_01_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_01_hx3 : SourcePowerBound
    (powerBoxCross 16 16 8 half_19_01_φ3) (92936890039/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 16) (u := 14) (t := 17)
    (D := 8) (ψ := (485659333/10000000000 : ℝ)) half_19_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_01_bounds3 l).1) (fun l => (half_19_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, half_19_01_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_01) (half_17_01)
    (by simpa only [half_19_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_19_01_hx4)
  exact h.weaken (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, half_19_01_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_01_hx2 : SourcePowerBound
    (powerBoxCross 16 17 4 half_19_01_φ2) (52001682891/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 17) (u := 15) (t := 18)
    (D := 4) (ψ := (123136481/2500000000 : ℝ)) half_19_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_01_bounds2 l).1) (fun l => (half_19_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, half_19_01_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_01) (half_18_01)
    (by simpa only [half_19_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_19_01_hx3)
  exact h.weaken (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, half_19_01_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_01_hx1 : SourcePowerBound
    (powerBoxCross 16 18 2 half_19_01_φ1) (233099739187/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 18) (u := 16) (t := 19)
    (D := 2) (ψ := (12531451/250000000 : ℝ)) half_19_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_01_bounds1 l).1) (fun l => (half_19_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, half_19_01_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_01) (chord_14)
    (by simpa only [half_19_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_19_01_hx2)
  exact h.weaken (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, half_19_01_total7, parameterExponent, curveLoss, dyadicExponent])

theorem half_19_01 : AdmissibleExponent 16 38 (252564180267/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 17) (ψ := (69515861/1250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_18_01)
    (by simpa only [half_19_01_φ1] using half_19_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, half_19_01_total7, parameterExponent, curveLoss, dyadicExponent])

theorem chord_21 : AdmissibleExponent 16 40 (122056863391/4500000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 40) (t := (8/9 : ℝ))
    (half_19_01) (half_28_00)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem chord_23 : AdmissibleExponent 16 44 (462876093109/15000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 44) (t := (2/3 : ℝ))
    (half_19_01) (half_28_00)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_20_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (35143931/625000000 : ℝ)

private theorem half_20_01_total1 : total half_20_01_φ1=(35143931/625000000 : ℝ) := by
  norm_num [half_20_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_20_01_bounds1 : ∀ l,0≤half_20_01_φ1 l ∧ half_20_01_φ1 l≤1 ∧
    0≤shiftExponents 16 half_20_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (35143931/625000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_20_01_φ2 : Fin 2 → ℝ := Fin.snoc half_20_01_φ1 (254711839/5000000000 : ℝ)

private theorem half_20_01_total2 : total half_20_01_φ2=(535863287/5000000000 : ℝ) := by
  change total (Fin.snoc half_20_01_φ1 (254711839/5000000000 : ℝ))=(535863287/5000000000 : ℝ)
  rw [alternate_total_snoc,half_20_01_total1]
  norm_num

private theorem half_20_01_bounds2 : ∀ l,0≤half_20_01_φ2 l ∧ half_20_01_φ2 l≤1 ∧
    0≤shiftExponents 16 half_20_01_φ2 l :=
  alternate_bounds_snoc half_20_01_φ1 (254711839/5000000000 : ℝ) half_20_01_bounds1 (by norm_num)

private def half_20_01_φ3 : Fin 3 → ℝ := Fin.snoc half_20_01_φ2 (250390177/5000000000 : ℝ)

private theorem half_20_01_total3 : total half_20_01_φ3=(98281683/625000000 : ℝ) := by
  change total (Fin.snoc half_20_01_φ2 (250390177/5000000000 : ℝ))=(98281683/625000000 : ℝ)
  rw [alternate_total_snoc,half_20_01_total2]
  norm_num

private theorem half_20_01_bounds3 : ∀ l,0≤half_20_01_φ3 l ∧ half_20_01_φ3 l≤1 ∧
    0≤shiftExponents 16 half_20_01_φ3 l :=
  alternate_bounds_snoc half_20_01_φ2 (250390177/5000000000 : ℝ) half_20_01_bounds2 (by norm_num)

private def half_20_01_φ4 : Fin 4 → ℝ := Fin.snoc half_20_01_φ3 (246260549/5000000000 : ℝ)

private theorem half_20_01_total4 : total half_20_01_φ4=(1032514013/5000000000 : ℝ) := by
  change total (Fin.snoc half_20_01_φ3 (246260549/5000000000 : ℝ))=(1032514013/5000000000 : ℝ)
  rw [alternate_total_snoc,half_20_01_total3]
  norm_num

private theorem half_20_01_bounds4 : ∀ l,0≤half_20_01_φ4 l ∧ half_20_01_φ4 l≤1 ∧
    0≤shiftExponents 16 half_20_01_φ4 l :=
  alternate_bounds_snoc half_20_01_φ3 (246260549/5000000000 : ℝ) half_20_01_bounds3 (by norm_num)

private def half_20_01_φ5 : Fin 5 → ℝ := Fin.snoc half_20_01_φ4 (486954947/10000000000 : ℝ)

private theorem half_20_01_total5 : total half_20_01_φ5=(2551982973/10000000000 : ℝ) := by
  change total (Fin.snoc half_20_01_φ4 (486954947/10000000000 : ℝ))=(2551982973/10000000000 : ℝ)
  rw [alternate_total_snoc,half_20_01_total4]
  norm_num

private theorem half_20_01_bounds5 : ∀ l,0≤half_20_01_φ5 l ∧ half_20_01_φ5 l≤1 ∧
    0≤shiftExponents 16 half_20_01_φ5 l :=
  alternate_bounds_snoc half_20_01_φ4 (486954947/10000000000 : ℝ) half_20_01_bounds4 (by norm_num)

private def half_20_01_φ6 : Fin 6 → ℝ := Fin.snoc half_20_01_φ5 (487189063/10000000000 : ℝ)

private theorem half_20_01_total6 : total half_20_01_φ6=(759793009/2500000000 : ℝ) := by
  change total (Fin.snoc half_20_01_φ5 (487189063/10000000000 : ℝ))=(759793009/2500000000 : ℝ)
  rw [alternate_total_snoc,half_20_01_total5]
  norm_num

private theorem half_20_01_bounds6 : ∀ l,0≤half_20_01_φ6 l ∧ half_20_01_φ6 l≤1 ∧
    0≤shiftExponents 16 half_20_01_φ6 l :=
  alternate_bounds_snoc half_20_01_φ5 (487189063/10000000000 : ℝ) half_20_01_bounds5 (by norm_num)

private def half_20_01_φ7 : Fin 7 → ℝ := Fin.snoc half_20_01_φ6 (464055197/10000000000 : ℝ)

private theorem half_20_01_total7 : total half_20_01_φ7=(3503227233/10000000000 : ℝ) := by
  change total (Fin.snoc half_20_01_φ6 (464055197/10000000000 : ℝ))=(3503227233/10000000000 : ℝ)
  rw [alternate_total_snoc,half_20_01_total6]
  norm_num

private theorem half_20_01_bounds7 : ∀ l,0≤half_20_01_φ7 l ∧ half_20_01_φ7 l≤1 ∧
    0≤shiftExponents 16 half_20_01_φ7 l :=
  alternate_bounds_snoc half_20_01_φ6 (464055197/10000000000 : ℝ) half_20_01_bounds6 (by norm_num)

private def half_20_01_φ8 : Fin 8 → ℝ := Fin.snoc half_20_01_φ7 (54139773/1250000000 : ℝ)

private theorem half_20_01_total8 : total half_20_01_φ8=(3936345417/10000000000 : ℝ) := by
  change total (Fin.snoc half_20_01_φ7 (54139773/1250000000 : ℝ))=(3936345417/10000000000 : ℝ)
  rw [alternate_total_snoc,half_20_01_total7]
  norm_num

private theorem half_20_01_bounds8 : ∀ l,0≤half_20_01_φ8 l ∧ half_20_01_φ8 l≤1 ∧
    0≤shiftExponents 16 half_20_01_φ8 l :=
  alternate_bounds_snoc half_20_01_φ7 (54139773/1250000000 : ℝ) half_20_01_bounds7 (by norm_num)

private def half_20_01_φ9 : Fin 9 → ℝ := Fin.snoc half_20_01_φ8 (202121819/5000000000 : ℝ)

private theorem half_20_01_total9 : total half_20_01_φ9=(868117811/2000000000 : ℝ) := by
  change total (Fin.snoc half_20_01_φ8 (202121819/5000000000 : ℝ))=(868117811/2000000000 : ℝ)
  rw [alternate_total_snoc,half_20_01_total8]
  norm_num

private theorem half_20_01_bounds9 : ∀ l,0≤half_20_01_φ9 l ∧ half_20_01_φ9 l≤1 ∧
    0≤shiftExponents 16 half_20_01_φ9 l :=
  alternate_bounds_snoc half_20_01_φ8 (202121819/5000000000 : ℝ) half_20_01_bounds8 (by norm_num)

private theorem half_20_01_prefix : PrefixCondition 16 half_20_01_φ9 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_20_01_φ1, half_20_01_φ2, half_20_01_φ3, half_20_01_φ4, half_20_01_φ5, half_20_01_φ6, half_20_01_φ7, half_20_01_φ8, half_20_01_φ9, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_20_01_hF1 : SourcePowerBound
    (paddedMoment 16 0 1 512 half_20_01_φ9) (1395646567/400000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 16) (j := 9) (r := 0) (n := 0) (D := 512)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_20_01_φ9
    (fun i => (half_20_01_bounds9 i).1) (fun i => (half_20_01_bounds9 i).2.1)
    (fun i => (half_20_01_bounds9 i).2.2) half_20_01_prefix
  convert h using 1 <;> norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, half_20_01_total7, half_20_01_total8, half_20_01_total9, parameterExponent, curveLoss, dyadicExponent]

private theorem half_20_01_hx9 : SourcePowerBound
    (powerBoxCross 16 11 512 half_20_01_φ9) (20953156601/2000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 11) (r := 1) (v := 0) (w := 22) (D := 512)
    (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_20_01_φ9 (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, half_20_01_total7, half_20_01_total8, half_20_01_total9, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, half_20_01_total7, half_20_01_total8, half_20_01_total9, parameterExponent, curveLoss, dyadicExponent]) half_20_01_hF1
    (admissibleExponent_zero 16) (chord_23)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, half_20_01_total7, half_20_01_total8, half_20_01_total9, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_01_hx8 : SourcePowerBound
    (powerBoxCross 16 12 256 half_20_01_φ8) (22887507063/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 8) (s := 12) (u := 10) (t := 13)
    (D := 256) (ψ := (202121819/5000000000 : ℝ)) half_20_01_φ8
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_01_bounds8 l).1) (fun l => (half_20_01_bounds8 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, half_20_01_total7, half_20_01_total8, half_20_01_total9, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_11) (SeedCompletionHigher16SimpleSeeds.degree16_half_13)
    (by simpa only [half_20_01_φ9, show (2:ℝ)*256=512 by norm_num] using half_20_01_hx9)
  exact h.weaken (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, half_20_01_total7, half_20_01_total8, half_20_01_total9, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_01_hx7 : SourcePowerBound
    (powerBoxCross 16 13 128 half_20_01_φ7) (126442385719/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 7) (s := 13) (u := 11) (t := 14)
    (D := 128) (ψ := (54139773/1250000000 : ℝ)) half_20_01_φ7
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_01_bounds7 l).1) (fun l => (half_20_01_bounds7 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, half_20_01_total7, half_20_01_total8, half_20_01_total9, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_12) (SeedCompletionHigher16SimpleSeeds.degree16_half_14)
    (by simpa only [half_20_01_φ8, show (2:ℝ)*128=256 by norm_num] using half_20_01_hx8)
  exact h.weaken (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, half_20_01_total7, half_20_01_total8, half_20_01_total9, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_01_hx6 : SourcePowerBound
    (powerBoxCross 16 14 64 half_20_01_φ6) (141172365599/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 6) (s := 14) (u := 12) (t := 15)
    (D := 64) (ψ := (464055197/10000000000 : ℝ)) half_20_01_φ6
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_01_bounds6 l).1) (fun l => (half_20_01_bounds6 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, half_20_01_total7, half_20_01_total8, half_20_01_total9, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_13) (half_15_01)
    (by simpa only [half_20_01_φ7, show (2:ℝ)*64=128 by norm_num] using half_20_01_hx7)
  exact h.weaken (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, half_20_01_total7, half_20_01_total8, half_20_01_total9, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_01_hx5 : SourcePowerBound
    (powerBoxCross 16 15 32 half_20_01_φ5) (79245496661/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 5) (s := 15) (u := 13) (t := 16)
    (D := 32) (ψ := (487189063/10000000000 : ℝ)) half_20_01_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_01_bounds5 l).1) (fun l => (half_20_01_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, half_20_01_total7, half_20_01_total8, half_20_01_total9, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_14) (half_16_01)
    (by simpa only [half_20_01_φ6, show (2:ℝ)*32=64 by norm_num] using half_20_01_hx6)
  exact h.weaken (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, half_20_01_total7, half_20_01_total8, half_20_01_total9, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_01_hx4 : SourcePowerBound
    (powerBoxCross 16 16 16 half_20_01_φ4) (177708398317/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 16) (u := 14) (t := 17)
    (D := 16) (ψ := (486954947/10000000000 : ℝ)) half_20_01_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_01_bounds4 l).1) (fun l => (half_20_01_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, half_20_01_total7, half_20_01_total8, half_20_01_total9, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_01) (half_17_01)
    (by simpa only [half_20_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_20_01_hx5)
  exact h.weaken (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, half_20_01_total7, half_20_01_total8, half_20_01_total9, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_01_hx3 : SourcePowerBound
    (powerBoxCross 16 17 8 half_20_01_φ3) (99495425107/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 17) (u := 15) (t := 18)
    (D := 8) (ψ := (246260549/5000000000 : ℝ)) half_20_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_01_bounds3 l).1) (fun l => (half_20_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, half_20_01_total7, half_20_01_total8, half_20_01_total9, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_01) (half_18_01)
    (by simpa only [half_20_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_20_01_hx4)
  exact h.weaken (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, half_20_01_total7, half_20_01_total8, half_20_01_total9, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_01_hx2 : SourcePowerBound
    (powerBoxCross 16 18 4 half_20_01_φ2) (44493690919/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 18) (u := 16) (t := 19)
    (D := 4) (ψ := (250390177/5000000000 : ℝ)) half_20_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_01_bounds2 l).1) (fun l => (half_20_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, half_20_01_total7, half_20_01_total8, half_20_01_total9, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_01) (half_19_01)
    (by simpa only [half_20_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_20_01_hx3)
  exact h.weaken (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, half_20_01_total7, half_20_01_total8, half_20_01_total9, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_01_hx1 : SourcePowerBound
    (powerBoxCross 16 19 2 half_20_01_φ1) (124462363091/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 19) (u := 17) (t := 20)
    (D := 2) (ψ := (254711839/5000000000 : ℝ)) half_20_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_01_bounds1 l).1) (fun l => (half_20_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, half_20_01_total7, half_20_01_total8, half_20_01_total9, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_01) (chord_21)
    (by simpa only [half_20_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_20_01_hx2)
  exact h.weaken (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, half_20_01_total7, half_20_01_total8, half_20_01_total9, parameterExponent, curveLoss, dyadicExponent])

theorem half_20_01 : AdmissibleExponent 16 40 (134864966667/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 18) (ψ := (35143931/625000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_19_01)
    (by simpa only [half_20_01_φ1] using half_20_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, half_20_01_total7, half_20_01_total8, half_20_01_total9, parameterExponent, curveLoss, dyadicExponent])

theorem chord_29 : AdmissibleExponent 16 42 (2885695809299/100000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 42) (t := (9/10 : ℝ))
    (half_20_01) (half_30_00)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_21_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (283894059/5000000000 : ℝ)

private theorem half_21_01_total1 : total half_21_01_φ1=(283894059/5000000000 : ℝ) := by
  norm_num [half_21_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_21_01_bounds1 : ∀ l,0≤half_21_01_φ1 l ∧ half_21_01_φ1 l≤1 ∧
    0≤shiftExponents 16 half_21_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (283894059/5000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_21_01_φ2 : Fin 2 → ℝ := Fin.snoc half_21_01_φ1 (10343037/200000000 : ℝ)

private theorem half_21_01_total2 : total half_21_01_φ2=(16952187/156250000 : ℝ) := by
  change total (Fin.snoc half_21_01_φ1 (10343037/200000000 : ℝ))=(16952187/156250000 : ℝ)
  rw [alternate_total_snoc,half_21_01_total1]
  norm_num

private theorem half_21_01_bounds2 : ∀ l,0≤half_21_01_φ2 l ∧ half_21_01_φ2 l≤1 ∧
    0≤shiftExponents 16 half_21_01_φ2 l :=
  alternate_bounds_snoc half_21_01_φ1 (10343037/200000000 : ℝ) half_21_01_bounds1 (by norm_num)

private def half_21_01_φ3 : Fin 3 → ℝ := Fin.snoc half_21_01_φ2 (101740249/2000000000 : ℝ)

private theorem half_21_01_total3 : total half_21_01_φ3=(1593641213/10000000000 : ℝ) := by
  change total (Fin.snoc half_21_01_φ2 (101740249/2000000000 : ℝ))=(1593641213/10000000000 : ℝ)
  rw [alternate_total_snoc,half_21_01_total2]
  norm_num

private theorem half_21_01_bounds3 : ∀ l,0≤half_21_01_φ3 l ∧ half_21_01_φ3 l≤1 ∧
    0≤shiftExponents 16 half_21_01_φ3 l :=
  alternate_bounds_snoc half_21_01_φ2 (101740249/2000000000 : ℝ) half_21_01_bounds2 (by norm_num)

private def half_21_01_φ4 : Fin 4 → ℝ := Fin.snoc half_21_01_φ3 (250020277/5000000000 : ℝ)

private theorem half_21_01_total4 : total half_21_01_φ4=(2093681767/10000000000 : ℝ) := by
  change total (Fin.snoc half_21_01_φ3 (250020277/5000000000 : ℝ))=(2093681767/10000000000 : ℝ)
  rw [alternate_total_snoc,half_21_01_total3]
  norm_num

private theorem half_21_01_bounds4 : ∀ l,0≤half_21_01_φ4 l ∧ half_21_01_φ4 l≤1 ∧
    0≤shiftExponents 16 half_21_01_φ4 l :=
  alternate_bounds_snoc half_21_01_φ3 (250020277/5000000000 : ℝ) half_21_01_bounds3 (by norm_num)

private def half_21_01_φ5 : Fin 5 → ℝ := Fin.snoc half_21_01_φ4 (245898263/5000000000 : ℝ)

private theorem half_21_01_total5 : total half_21_01_φ5=(2585478293/10000000000 : ℝ) := by
  change total (Fin.snoc half_21_01_φ4 (245898263/5000000000 : ℝ))=(2585478293/10000000000 : ℝ)
  rw [alternate_total_snoc,half_21_01_total4]
  norm_num

private theorem half_21_01_bounds5 : ∀ l,0≤half_21_01_φ5 l ∧ half_21_01_φ5 l≤1 ∧
    0≤shiftExponents 16 half_21_01_φ5 l :=
  alternate_bounds_snoc half_21_01_φ4 (245898263/5000000000 : ℝ) half_21_01_bounds4 (by norm_num)

private def half_21_01_φ6 : Fin 6 → ℝ := Fin.snoc half_21_01_φ5 (486290173/10000000000 : ℝ)

private theorem half_21_01_total6 : total half_21_01_φ6=(1535884233/5000000000 : ℝ) := by
  change total (Fin.snoc half_21_01_φ5 (486290173/10000000000 : ℝ))=(1535884233/5000000000 : ℝ)
  rw [alternate_total_snoc,half_21_01_total5]
  norm_num

private theorem half_21_01_bounds6 : ∀ l,0≤half_21_01_φ6 l ∧ half_21_01_φ6 l≤1 ∧
    0≤shiftExponents 16 half_21_01_φ6 l :=
  alternate_bounds_snoc half_21_01_φ5 (486290173/10000000000 : ℝ) half_21_01_bounds5 (by norm_num)

private def half_21_01_φ7 : Fin 7 → ℝ := Fin.snoc half_21_01_φ6 (230941051/5000000000 : ℝ)

private theorem half_21_01_total7 : total half_21_01_φ7=(441706321/1250000000 : ℝ) := by
  change total (Fin.snoc half_21_01_φ6 (230941051/5000000000 : ℝ))=(441706321/1250000000 : ℝ)
  rw [alternate_total_snoc,half_21_01_total6]
  norm_num

private theorem half_21_01_bounds7 : ∀ l,0≤half_21_01_φ7 l ∧ half_21_01_φ7 l≤1 ∧
    0≤shiftExponents 16 half_21_01_φ7 l :=
  alternate_bounds_snoc half_21_01_φ6 (230941051/5000000000 : ℝ) half_21_01_bounds6 (by norm_num)

private def half_21_01_φ8 : Fin 8 → ℝ := Fin.snoc half_21_01_φ7 (215544981/5000000000 : ℝ)

private theorem half_21_01_total8 : total half_21_01_φ8=(396474053/1000000000 : ℝ) := by
  change total (Fin.snoc half_21_01_φ7 (215544981/5000000000 : ℝ))=(396474053/1000000000 : ℝ)
  rw [alternate_total_snoc,half_21_01_total7]
  norm_num

private theorem half_21_01_bounds8 : ∀ l,0≤half_21_01_φ8 l ∧ half_21_01_φ8 l≤1 ∧
    0≤shiftExponents 16 half_21_01_φ8 l :=
  alternate_bounds_snoc half_21_01_φ7 (215544981/5000000000 : ℝ) half_21_01_bounds7 (by norm_num)

private def half_21_01_φ9 : Fin 9 → ℝ := Fin.snoc half_21_01_φ8 (402350631/10000000000 : ℝ)

private theorem half_21_01_total9 : total half_21_01_φ9=(4367091161/10000000000 : ℝ) := by
  change total (Fin.snoc half_21_01_φ8 (402350631/10000000000 : ℝ))=(4367091161/10000000000 : ℝ)
  rw [alternate_total_snoc,half_21_01_total8]
  norm_num

private theorem half_21_01_bounds9 : ∀ l,0≤half_21_01_φ9 l ∧ half_21_01_φ9 l≤1 ∧
    0≤shiftExponents 16 half_21_01_φ9 l :=
  alternate_bounds_snoc half_21_01_φ8 (402350631/10000000000 : ℝ) half_21_01_bounds8 (by norm_num)

private def half_21_01_φ10 : Fin 10 → ℝ := Fin.snoc half_21_01_φ9 (318780657/10000000000 : ℝ)

private theorem half_21_01_total10 : total half_21_01_φ10=(2342935909/5000000000 : ℝ) := by
  change total (Fin.snoc half_21_01_φ9 (318780657/10000000000 : ℝ))=(2342935909/5000000000 : ℝ)
  rw [alternate_total_snoc,half_21_01_total9]
  norm_num

private theorem half_21_01_bounds10 : ∀ l,0≤half_21_01_φ10 l ∧ half_21_01_φ10 l≤1 ∧
    0≤shiftExponents 16 half_21_01_φ10 l :=
  alternate_bounds_snoc half_21_01_φ9 (318780657/10000000000 : ℝ) half_21_01_bounds9 (by norm_num)

private def half_21_01_φ11 : Fin 11 → ℝ := Fin.snoc half_21_01_φ10 (0/1 : ℝ)

private theorem half_21_01_total11 : total half_21_01_φ11=(2342935909/5000000000 : ℝ) := by
  change total (Fin.snoc half_21_01_φ10 (0/1 : ℝ))=(2342935909/5000000000 : ℝ)
  rw [alternate_total_snoc,half_21_01_total10]
  norm_num

private theorem half_21_01_bounds11 : ∀ l,0≤half_21_01_φ11 l ∧ half_21_01_φ11 l≤1 ∧
    0≤shiftExponents 16 half_21_01_φ11 l :=
  alternate_bounds_snoc half_21_01_φ10 (0/1 : ℝ) half_21_01_bounds10 (by norm_num)

private theorem half_21_01_prefix : PrefixCondition 16 half_21_01_φ11 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_21_01_φ1, half_21_01_φ2, half_21_01_φ3, half_21_01_φ4, half_21_01_φ5, half_21_01_φ6, half_21_01_φ7, half_21_01_φ8, half_21_01_φ9, half_21_01_φ10, half_21_01_φ11, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_21_01_hF1 : SourcePowerBound
    (paddedMoment 16 0 1 2048 half_21_01_φ11) (4971192273/1000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 16) (j := 11) (r := 0) (n := 0) (D := 2048)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_21_01_φ11
    (fun i => (half_21_01_bounds11 i).1) (fun i => (half_21_01_bounds11 i).2.1)
    (fun i => (half_21_01_bounds11 i).2.2) half_21_01_prefix
  convert h using 1 <;> norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, half_21_01_total9, half_21_01_total10, half_21_01_total11, parameterExponent, curveLoss, dyadicExponent]

private theorem half_21_01_hx11 : SourcePowerBound
    (powerBoxCross 16 10 2048 half_21_01_φ11) (48262466689/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 10) (r := 1) (v := 0) (w := 20) (D := 2048)
    (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_21_01_φ11 (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, half_21_01_total9, half_21_01_total10, half_21_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, half_21_01_total9, half_21_01_total10, half_21_01_total11, parameterExponent, curveLoss, dyadicExponent]) half_21_01_hF1
    (admissibleExponent_zero 16) (half_20_01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, half_21_01_total9, half_21_01_total10, half_21_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_01_hx10 : SourcePowerBound
    (powerBoxCross 16 11 1024 half_21_01_φ10) (102658843723/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 10) (s := 11) (u := 9) (t := 12)
    (D := 1024) (ψ := (0/1 : ℝ)) half_21_01_φ10
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_01_bounds10 l).1) (fun l => (half_21_01_bounds10 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, half_21_01_total9, half_21_01_total10, half_21_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_10) (SeedCompletionHigher16SimpleSeeds.degree16_half_12)
    (by simpa only [half_21_01_φ11, show (2:ℝ)*1024=2048 by norm_num] using half_21_01_hx11)
  exact h.weaken (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, half_21_01_total9, half_21_01_total10, half_21_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_01_hx9 : SourcePowerBound
    (powerBoxCross 16 12 512 half_21_01_φ9) (22178745007/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 9) (s := 12) (u := 10) (t := 13)
    (D := 512) (ψ := (318780657/10000000000 : ℝ)) half_21_01_φ9
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_01_bounds9 l).1) (fun l => (half_21_01_bounds9 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, half_21_01_total9, half_21_01_total10, half_21_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_11) (SeedCompletionHigher16SimpleSeeds.degree16_half_13)
    (by simpa only [half_21_01_φ10, show (2:ℝ)*512=1024 by norm_num] using half_21_01_hx10)
  exact h.weaken (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, half_21_01_total9, half_21_01_total10, half_21_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_01_hx8 : SourcePowerBound
    (powerBoxCross 16 13 256 half_21_01_φ8) (3047788199/250000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 8) (s := 13) (u := 11) (t := 14)
    (D := 256) (ψ := (402350631/10000000000 : ℝ)) half_21_01_φ8
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_01_bounds8 l).1) (fun l => (half_21_01_bounds8 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, half_21_01_total9, half_21_01_total10, half_21_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_12) (SeedCompletionHigher16SimpleSeeds.degree16_half_14)
    (by simpa only [half_21_01_φ9, show (2:ℝ)*256=512 by norm_num] using half_21_01_hx9)
  exact h.weaken (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, half_21_01_total9, half_21_01_total10, half_21_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_01_hx7 : SourcePowerBound
    (powerBoxCross 16 14 128 half_21_01_φ7) (3379320387/250000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 7) (s := 14) (u := 12) (t := 15)
    (D := 128) (ψ := (215544981/5000000000 : ℝ)) half_21_01_φ7
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_01_bounds7 l).1) (fun l => (half_21_01_bounds7 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, half_21_01_total9, half_21_01_total10, half_21_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_13) (half_15_01)
    (by simpa only [half_21_01_φ8, show (2:ℝ)*128=256 by norm_num] using half_21_01_hx8)
  exact h.weaken (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, half_21_01_total9, half_21_01_total10, half_21_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_01_hx6 : SourcePowerBound
    (powerBoxCross 16 15 64 half_21_01_φ6) (75492207427/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 6) (s := 15) (u := 13) (t := 16)
    (D := 64) (ψ := (230941051/5000000000 : ℝ)) half_21_01_φ6
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_01_bounds6 l).1) (fun l => (half_21_01_bounds6 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, half_21_01_total9, half_21_01_total10, half_21_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_14) (half_16_01)
    (by simpa only [half_21_01_φ7, show (2:ℝ)*64=128 by norm_num] using half_21_01_hx7)
  exact h.weaken (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, half_21_01_total9, half_21_01_total10, half_21_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_01_hx5 : SourcePowerBound
    (powerBoxCross 16 16 32 half_21_01_φ5) (16934304293/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 5) (s := 16) (u := 14) (t := 17)
    (D := 32) (ψ := (486290173/10000000000 : ℝ)) half_21_01_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_01_bounds5 l).1) (fun l => (half_21_01_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, half_21_01_total9, half_21_01_total10, half_21_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_01) (half_17_01)
    (by simpa only [half_21_01_φ6, show (2:ℝ)*32=64 by norm_num] using half_21_01_hx6)
  exact h.weaken (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, half_21_01_total9, half_21_01_total10, half_21_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_01_hx4 : SourcePowerBound
    (powerBoxCross 16 17 16 half_21_01_φ4) (189747422523/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 17) (u := 15) (t := 18)
    (D := 16) (ψ := (245898263/5000000000 : ℝ)) half_21_01_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_01_bounds4 l).1) (fun l => (half_21_01_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, half_21_01_total9, half_21_01_total10, half_21_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_01) (half_18_01)
    (by simpa only [half_21_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_21_01_hx5)
  exact h.weaken (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, half_21_01_total9, half_21_01_total10, half_21_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_01_hx3 : SourcePowerBound
    (powerBoxCross 16 18 8 half_21_01_φ3) (212329327109/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 18) (u := 16) (t := 19)
    (D := 8) (ψ := (250020277/5000000000 : ℝ)) half_21_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_01_bounds3 l).1) (fun l => (half_21_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, half_21_01_total9, half_21_01_total10, half_21_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_01) (half_19_01)
    (by simpa only [half_21_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_21_01_hx4)
  exact h.weaken (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, half_21_01_total9, half_21_01_total10, half_21_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_01_hx2 : SourcePowerBound
    (powerBoxCross 16 19 4 half_21_01_φ2) (237162812987/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 19) (u := 17) (t := 20)
    (D := 4) (ψ := (101740249/2000000000 : ℝ)) half_21_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_01_bounds2 l).1) (fun l => (half_21_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, half_21_01_total9, half_21_01_total10, half_21_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_01) (half_20_01)
    (by simpa only [half_21_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_21_01_hx3)
  exact h.weaken (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, half_21_01_total9, half_21_01_total10, half_21_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_01_hx1 : SourcePowerBound
    (powerBoxCross 16 20 2 half_21_01_φ1) (16561423521/625000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 20) (u := 18) (t := 21)
    (D := 2) (ψ := (10343037/200000000 : ℝ)) half_21_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_01_bounds1 l).1) (fun l => (half_21_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, half_21_01_total9, half_21_01_total10, half_21_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_19_01) (chord_29)
    (by simpa only [half_21_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_21_01_hx2)
  exact h.weaken (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, half_21_01_total9, half_21_01_total10, half_21_01_total11, parameterExponent, curveLoss, dyadicExponent])

theorem half_21_01 : AdmissibleExponent 16 42 (143563256469/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 19) (ψ := (283894059/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_20_01)
    (by simpa only [half_21_01_φ1] using half_21_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, half_21_01_total9, half_21_01_total10, half_21_01_total11, parameterExponent, curveLoss, dyadicExponent])

theorem chord_38 : AdmissibleExponent 16 44 (2755138512797/90000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 44) (t := (8/9 : ℝ))
    (half_21_01) (half_30_00)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_22_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (573335357/10000000000 : ℝ)

private theorem half_22_01_total1 : total half_22_01_φ1=(573335357/10000000000 : ℝ) := by
  norm_num [half_22_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_22_01_bounds1 : ∀ l,0≤half_22_01_φ1 l ∧ half_22_01_φ1 l≤1 ∧
    0≤shiftExponents 16 half_22_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (573335357/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_22_01_φ2 : Fin 2 → ℝ := Fin.snoc half_22_01_φ1 (262349281/5000000000 : ℝ)

private theorem half_22_01_total2 : total half_22_01_φ2=(1098033919/10000000000 : ℝ) := by
  change total (Fin.snoc half_22_01_φ1 (262349281/5000000000 : ℝ))=(1098033919/10000000000 : ℝ)
  rw [alternate_total_snoc,half_22_01_total1]
  norm_num

private theorem half_22_01_bounds2 : ∀ l,0≤half_22_01_φ2 l ∧ half_22_01_φ2 l≤1 ∧
    0≤shiftExponents 16 half_22_01_φ2 l :=
  alternate_bounds_snoc half_22_01_φ1 (262349281/5000000000 : ℝ) half_22_01_bounds1 (by norm_num)

private def half_22_01_φ3 : Fin 3 → ℝ := Fin.snoc half_22_01_φ2 (516720731/10000000000 : ℝ)

private theorem half_22_01_total3 : total half_22_01_φ3=(32295093/200000000 : ℝ) := by
  change total (Fin.snoc half_22_01_φ2 (516720731/10000000000 : ℝ))=(32295093/200000000 : ℝ)
  rw [alternate_total_snoc,half_22_01_total2]
  norm_num

private theorem half_22_01_bounds3 : ∀ l,0≤half_22_01_φ3 l ∧ half_22_01_φ3 l≤1 ∧
    0≤shiftExponents 16 half_22_01_φ3 l :=
  alternate_bounds_snoc half_22_01_φ2 (516720731/10000000000 : ℝ) half_22_01_bounds2 (by norm_num)

private def half_22_01_φ4 : Fin 4 → ℝ := Fin.snoc half_22_01_φ3 (254329003/5000000000 : ℝ)

private theorem half_22_01_total4 : total half_22_01_φ4=(132713291/625000000 : ℝ) := by
  change total (Fin.snoc half_22_01_φ3 (254329003/5000000000 : ℝ))=(132713291/625000000 : ℝ)
  rw [alternate_total_snoc,half_22_01_total3]
  norm_num

private theorem half_22_01_bounds4 : ∀ l,0≤half_22_01_φ4 l ∧ half_22_01_φ4 l≤1 ∧
    0≤shiftExponents 16 half_22_01_φ4 l :=
  alternate_bounds_snoc half_22_01_φ3 (254329003/5000000000 : ℝ) half_22_01_bounds3 (by norm_num)

private def half_22_01_φ5 : Fin 5 → ℝ := Fin.snoc half_22_01_φ4 (125278667/2500000000 : ℝ)

private theorem half_22_01_total5 : total half_22_01_φ5=(656131831/2500000000 : ℝ) := by
  change total (Fin.snoc half_22_01_φ4 (125278667/2500000000 : ℝ))=(656131831/2500000000 : ℝ)
  rw [alternate_total_snoc,half_22_01_total4]
  norm_num

private theorem half_22_01_bounds5 : ∀ l,0≤half_22_01_φ5 l ∧ half_22_01_φ5 l≤1 ∧
    0≤shiftExponents 16 half_22_01_φ5 l :=
  alternate_bounds_snoc half_22_01_φ4 (125278667/2500000000 : ℝ) half_22_01_bounds4 (by norm_num)

private def half_22_01_φ6 : Fin 6 → ℝ := Fin.snoc half_22_01_φ5 (245849089/5000000000 : ℝ)

private theorem half_22_01_total6 : total half_22_01_φ6=(1558112751/5000000000 : ℝ) := by
  change total (Fin.snoc half_22_01_φ5 (245849089/5000000000 : ℝ))=(1558112751/5000000000 : ℝ)
  rw [alternate_total_snoc,half_22_01_total5]
  norm_num

private theorem half_22_01_bounds6 : ∀ l,0≤half_22_01_φ6 l ∧ half_22_01_φ6 l≤1 ∧
    0≤shiftExponents 16 half_22_01_φ6 l :=
  alternate_bounds_snoc half_22_01_φ5 (245849089/5000000000 : ℝ) half_22_01_bounds5 (by norm_num)

private def half_22_01_φ7 : Fin 7 → ℝ := Fin.snoc half_22_01_φ6 (458918299/10000000000 : ℝ)

private theorem half_22_01_total7 : total half_22_01_φ7=(3575143801/10000000000 : ℝ) := by
  change total (Fin.snoc half_22_01_φ6 (458918299/10000000000 : ℝ))=(3575143801/10000000000 : ℝ)
  rw [alternate_total_snoc,half_22_01_total6]
  norm_num

private theorem half_22_01_bounds7 : ∀ l,0≤half_22_01_φ7 l ∧ half_22_01_φ7 l≤1 ∧
    0≤shiftExponents 16 half_22_01_φ7 l :=
  alternate_bounds_snoc half_22_01_φ6 (458918299/10000000000 : ℝ) half_22_01_bounds6 (by norm_num)

private def half_22_01_φ8 : Fin 8 → ℝ := Fin.snoc half_22_01_φ7 (214161873/5000000000 : ℝ)

private theorem half_22_01_total8 : total half_22_01_φ8=(4003467547/10000000000 : ℝ) := by
  change total (Fin.snoc half_22_01_φ7 (214161873/5000000000 : ℝ))=(4003467547/10000000000 : ℝ)
  rw [alternate_total_snoc,half_22_01_total7]
  norm_num

private theorem half_22_01_bounds8 : ∀ l,0≤half_22_01_φ8 l ∧ half_22_01_φ8 l≤1 ∧
    0≤shiftExponents 16 half_22_01_φ8 l :=
  alternate_bounds_snoc half_22_01_φ7 (214161873/5000000000 : ℝ) half_22_01_bounds7 (by norm_num)

private def half_22_01_φ9 : Fin 9 → ℝ := Fin.snoc half_22_01_φ8 (399768829/10000000000 : ℝ)

private theorem half_22_01_total9 : total half_22_01_φ9=(550404547/1250000000 : ℝ) := by
  change total (Fin.snoc half_22_01_φ8 (399768829/10000000000 : ℝ))=(550404547/1250000000 : ℝ)
  rw [alternate_total_snoc,half_22_01_total8]
  norm_num

private theorem half_22_01_bounds9 : ∀ l,0≤half_22_01_φ9 l ∧ half_22_01_φ9 l≤1 ∧
    0≤shiftExponents 16 half_22_01_φ9 l :=
  alternate_bounds_snoc half_22_01_φ8 (399768829/10000000000 : ℝ) half_22_01_bounds8 (by norm_num)

private def half_22_01_φ10 : Fin 10 → ℝ := Fin.snoc half_22_01_φ9 (318879297/10000000000 : ℝ)

private theorem half_22_01_total10 : total half_22_01_φ10=(4722115673/10000000000 : ℝ) := by
  change total (Fin.snoc half_22_01_φ9 (318879297/10000000000 : ℝ))=(4722115673/10000000000 : ℝ)
  rw [alternate_total_snoc,half_22_01_total9]
  norm_num

private theorem half_22_01_bounds10 : ∀ l,0≤half_22_01_φ10 l ∧ half_22_01_φ10 l≤1 ∧
    0≤shiftExponents 16 half_22_01_φ10 l :=
  alternate_bounds_snoc half_22_01_φ9 (318879297/10000000000 : ℝ) half_22_01_bounds9 (by norm_num)

private def half_22_01_φ11 : Fin 11 → ℝ := Fin.snoc half_22_01_φ10 (0/1 : ℝ)

private theorem half_22_01_total11 : total half_22_01_φ11=(4722115673/10000000000 : ℝ) := by
  change total (Fin.snoc half_22_01_φ10 (0/1 : ℝ))=(4722115673/10000000000 : ℝ)
  rw [alternate_total_snoc,half_22_01_total10]
  norm_num

private theorem half_22_01_bounds11 : ∀ l,0≤half_22_01_φ11 l ∧ half_22_01_φ11 l≤1 ∧
    0≤shiftExponents 16 half_22_01_φ11 l :=
  alternate_bounds_snoc half_22_01_φ10 (0/1 : ℝ) half_22_01_bounds10 (by norm_num)

private theorem half_22_01_prefix : PrefixCondition 16 half_22_01_φ11 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_22_01_φ1, half_22_01_φ2, half_22_01_φ3, half_22_01_φ4, half_22_01_φ5, half_22_01_φ6, half_22_01_φ7, half_22_01_φ8, half_22_01_φ9, half_22_01_φ10, half_22_01_φ11, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_22_01_hF1 : SourcePowerBound
    (paddedMoment 16 0 1 2048 half_22_01_φ11) (9833652981/2000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 16) (j := 11) (r := 0) (n := 0) (D := 2048)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_22_01_φ11
    (fun i => (half_22_01_bounds11 i).1) (fun i => (half_22_01_bounds11 i).2.1)
    (fun i => (half_22_01_bounds11 i).2.2) half_22_01_prefix
  convert h using 1 <;> norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, half_22_01_total10, half_22_01_total11, parameterExponent, curveLoss, dyadicExponent]

private theorem half_22_01_hx11 : SourcePowerBound
    (powerBoxCross 16 11 2048 half_22_01_φ11) (2107382913/200000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 11) (r := 1) (v := 0) (w := 22) (D := 2048)
    (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_22_01_φ11 (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, half_22_01_total10, half_22_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, half_22_01_total10, half_22_01_total11, parameterExponent, curveLoss, dyadicExponent]) half_22_01_hF1
    (admissibleExponent_zero 16) (chord_38)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, half_22_01_total10, half_22_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_01_hx10 : SourcePowerBound
    (powerBoxCross 16 12 1024 half_22_01_φ10) (436236381/40000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 10) (s := 12) (u := 10) (t := 13)
    (D := 1024) (ψ := (0/1 : ℝ)) half_22_01_φ10
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_01_bounds10 l).1) (fun l => (half_22_01_bounds10 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, half_22_01_total10, half_22_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_11) (SeedCompletionHigher16SimpleSeeds.degree16_half_13)
    (by simpa only [half_22_01_φ11, show (2:ℝ)*1024=2048 by norm_num] using half_22_01_hx11)
  exact h.weaken (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, half_22_01_total10, half_22_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_01_hx9 : SourcePowerBound
    (powerBoxCross 16 13 512 half_22_01_φ9) (29499622299/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 9) (s := 13) (u := 11) (t := 14)
    (D := 512) (ψ := (318879297/10000000000 : ℝ)) half_22_01_φ9
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_01_bounds9 l).1) (fun l => (half_22_01_bounds9 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, half_22_01_total10, half_22_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_12) (SeedCompletionHigher16SimpleSeeds.degree16_half_14)
    (by simpa only [half_22_01_φ10, show (2:ℝ)*512=1024 by norm_num] using half_22_01_hx10)
  exact h.weaken (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, half_22_01_total10, half_22_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_01_hx8 : SourcePowerBound
    (powerBoxCross 16 14 256 half_22_01_φ8) (64958889589/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 8) (s := 14) (u := 12) (t := 15)
    (D := 256) (ψ := (399768829/10000000000 : ℝ)) half_22_01_φ8
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_01_bounds8 l).1) (fun l => (half_22_01_bounds8 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, half_22_01_total10, half_22_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_13) (half_15_01)
    (by simpa only [half_22_01_φ9, show (2:ℝ)*256=512 by norm_num] using half_22_01_hx9)
  exact h.weaken (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, half_22_01_total10, half_22_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_01_hx7 : SourcePowerBound
    (powerBoxCross 16 15 128 half_22_01_φ7) (144028052891/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 7) (s := 15) (u := 13) (t := 16)
    (D := 128) (ψ := (214161873/5000000000 : ℝ)) half_22_01_φ7
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_01_bounds7 l).1) (fun l => (half_22_01_bounds7 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, half_22_01_total10, half_22_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_14) (half_16_01)
    (by simpa only [half_22_01_φ8, show (2:ℝ)*128=256 by norm_num] using half_22_01_hx8)
  exact h.weaken (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, half_22_01_total10, half_22_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_01_hx6 : SourcePowerBound
    (powerBoxCross 16 16 64 half_22_01_φ6) (160675561901/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 6) (s := 16) (u := 14) (t := 17)
    (D := 64) (ψ := (458918299/10000000000 : ℝ)) half_22_01_φ6
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_01_bounds6 l).1) (fun l => (half_22_01_bounds6 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, half_22_01_total10, half_22_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_01) (half_17_01)
    (by simpa only [half_22_01_φ7, show (2:ℝ)*64=128 by norm_num] using half_22_01_hx7)
  exact h.weaken (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, half_22_01_total10, half_22_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_01_hx5 : SourcePowerBound
    (powerBoxCross 16 17 32 half_22_01_φ5) (90088081753/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 5) (s := 17) (u := 15) (t := 18)
    (D := 32) (ψ := (245849089/5000000000 : ℝ)) half_22_01_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_01_bounds5 l).1) (fun l => (half_22_01_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, half_22_01_total10, half_22_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_01) (half_18_01)
    (by simpa only [half_22_01_φ6, show (2:ℝ)*32=64 by norm_num] using half_22_01_hx6)
  exact h.weaken (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, half_22_01_total10, half_22_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_01_hx4 : SourcePowerBound
    (powerBoxCross 16 18 16 half_22_01_φ4) (201898070147/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 18) (u := 16) (t := 19)
    (D := 16) (ψ := (125278667/2500000000 : ℝ)) half_22_01_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_01_bounds4 l).1) (fun l => (half_22_01_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, half_22_01_total10, half_22_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_01) (half_19_01)
    (by simpa only [half_22_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_22_01_hx5)
  exact h.weaken (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, half_22_01_total10, half_22_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_01_hx3 : SourcePowerBound
    (powerBoxCross 16 19 8 half_22_01_φ3) (112913736883/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 19) (u := 17) (t := 20)
    (D := 8) (ψ := (254329003/5000000000 : ℝ)) half_22_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_01_bounds3 l).1) (fun l => (half_22_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, half_22_01_total10, half_22_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_01) (half_20_01)
    (by simpa only [half_22_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_22_01_hx4)
  exact h.weaken (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, half_22_01_total10, half_22_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_01_hx2 : SourcePowerBound
    (powerBoxCross 16 20 4 half_22_01_φ2) (252037339971/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 20) (u := 18) (t := 21)
    (D := 4) (ψ := (516720731/10000000000 : ℝ)) half_22_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_01_bounds2 l).1) (fun l => (half_22_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, half_22_01_total10, half_22_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_19_01) (half_21_01)
    (by simpa only [half_22_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_22_01_hx3)
  exact h.weaken (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, half_22_01_total10, half_22_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_01_hx1 : SourcePowerBound
    (powerBoxCross 16 21 2 half_22_01_φ1) (281237870129/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 21) (u := 19) (t := 22)
    (D := 2) (ψ := (262349281/5000000000 : ℝ)) half_22_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_01_bounds1 l).1) (fun l => (half_22_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, half_22_01_total10, half_22_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_20_01) (chord_38)
    (by simpa only [half_22_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_22_01_hx2)
  exact h.weaken (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, half_22_01_total10, half_22_01_total11, parameterExponent, curveLoss, dyadicExponent])

theorem half_22_01 : AdmissibleExponent 16 44 (152372309883/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 20) (ψ := (573335357/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_21_01)
    (by simpa only [half_22_01_φ1] using half_22_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, half_22_01_total10, half_22_01_total11, parameterExponent, curveLoss, dyadicExponent])

theorem chord_46 : AdmissibleExponent 16 46 (518267749531/16000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 46) (t := (7/8 : ℝ))
    (half_22_01) (half_30_00)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem chord_47 : AdmissibleExponent 16 48 (1372360268591/40000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 48) (t := (3/4 : ℝ))
    (half_22_01) (half_30_00)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

#print axioms chord_47
end Waring.SeedCompletionAlternate16Seeds
