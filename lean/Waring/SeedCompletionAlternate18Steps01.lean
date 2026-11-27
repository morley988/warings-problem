import Waring.SeedCompletionAlternate18Arithmetic

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionAlternate18Seeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges SeedCompletionDivisorPowerScales
open PolicyCompletionSharpResidualSource

theorem half_18_00 : AdmissibleExponent 18 36 (114417149829/5000000000 : ℝ) := by
  have h := endpoint_admissible (s := 16) (by norm_num : 0 < (18 : ℕ))
    (SeedCompletionHigher18SimpleSeeds.degree18_half_17) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_19_00 : AdmissibleExponent 18 38 (246121283011/10000000000 : ℝ) := by
  have h := endpoint_admissible (s := 17) (by norm_num : 0 < (18 : ℕ))
    (half_18_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_20_00 : AdmissibleExponent 18 40 (263558989511/10000000000 : ℝ) := by
  have h := endpoint_admissible (s := 18) (by norm_num : 0 < (18 : ℕ))
    (half_19_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_21_00 : AdmissibleExponent 18 42 (5622780913/200000000 : ℝ) := by
  have h := endpoint_admissible (s := 19) (by norm_num : 0 < (18 : ℕ))
    (half_20_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_22_00 : AdmissibleExponent 18 44 (149426771557/5000000000 : ℝ) := by
  have h := endpoint_admissible (s := 20) (by norm_num : 0 < (18 : ℕ))
    (half_21_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_23_00 : AdmissibleExponent 18 46 (316695012941/10000000000 : ℝ) := by
  have h := endpoint_admissible (s := 21) (by norm_num : 0 < (18 : ℕ))
    (half_22_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_24_00 : AdmissibleExponent 18 48 (334656401111/10000000000 : ℝ) := by
  have h := endpoint_admissible (s := 22) (by norm_num : 0 < (18 : ℕ))
    (half_23_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_25_00 : AdmissibleExponent 18 50 (176365522747/5000000000 : ℝ) := by
  have h := endpoint_admissible (s := 23) (by norm_num : 0 < (18 : ℕ))
    (half_24_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_26_00 : AdmissibleExponent 18 52 (185456327039/5000000000 : ℝ) := by
  have h := endpoint_admissible (s := 24) (by norm_num : 0 < (18 : ℕ))
    (half_25_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_27_00 : AdmissibleExponent 18 54 (389195284407/10000000000 : ℝ) := by
  have h := endpoint_admissible (s := 25) (by norm_num : 0 < (18 : ℕ))
    (half_26_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_28_00 : AdmissibleExponent 18 56 (407573324163/10000000000 : ℝ) := by
  have h := endpoint_admissible (s := 26) (by norm_num : 0 < (18 : ℕ))
    (half_27_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_29_00 : AdmissibleExponent 18 58 (426041472821/10000000000 : ℝ) := by
  have h := endpoint_admissible (s := 27) (by norm_num : 0 < (18 : ℕ))
    (half_28_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_30_00 : AdmissibleExponent 18 60 (444594724331/10000000000 : ℝ) := by
  have h := endpoint_admissible (s := 28) (by norm_num : 0 < (18 : ℕ))
    (half_29_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_31_00 : AdmissibleExponent 18 62 (231614175379/5000000000 : ℝ) := by
  have h := endpoint_admissible (s := 29) (by norm_num : 0 < (18 : ℕ))
    (half_30_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_18_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (472977381/10000000000 : ℝ)

private theorem half_18_01_total1 : total half_18_01_φ1=(472977381/10000000000 : ℝ) := by
  norm_num [half_18_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_18_01_bounds1 : ∀ l,0≤half_18_01_φ1 l ∧ half_18_01_φ1 l≤1 ∧
    0≤shiftExponents 18 half_18_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (472977381/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_18_01_φ2 : Fin 2 → ℝ := Fin.snoc half_18_01_φ1 (421055727/10000000000 : ℝ)

private theorem half_18_01_total2 : total half_18_01_φ2=(223508277/2500000000 : ℝ) := by
  change total (Fin.snoc half_18_01_φ1 (421055727/10000000000 : ℝ))=(223508277/2500000000 : ℝ)
  rw [alternate_total_snoc,half_18_01_total1]
  norm_num

private theorem half_18_01_bounds2 : ∀ l,0≤half_18_01_φ2 l ∧ half_18_01_φ2 l≤1 ∧
    0≤shiftExponents 18 half_18_01_φ2 l :=
  alternate_bounds_snoc half_18_01_φ1 (421055727/10000000000 : ℝ) half_18_01_bounds1 (by norm_num)

private def half_18_01_φ3 : Fin 3 → ℝ := Fin.snoc half_18_01_φ2 (16438117/400000000 : ℝ)

private theorem half_18_01_total3 : total half_18_01_φ3=(1304986033/10000000000 : ℝ) := by
  change total (Fin.snoc half_18_01_φ2 (16438117/400000000 : ℝ))=(1304986033/10000000000 : ℝ)
  rw [alternate_total_snoc,half_18_01_total2]
  norm_num

private theorem half_18_01_bounds3 : ∀ l,0≤half_18_01_φ3 l ∧ half_18_01_φ3 l≤1 ∧
    0≤shiftExponents 18 half_18_01_φ3 l :=
  alternate_bounds_snoc half_18_01_φ2 (16438117/400000000 : ℝ) half_18_01_bounds2 (by norm_num)

private def half_18_01_φ4 : Fin 4 → ℝ := Fin.snoc half_18_01_φ3 (49890629/1250000000 : ℝ)

private theorem half_18_01_total4 : total half_18_01_φ4=(340822213/2000000000 : ℝ) := by
  change total (Fin.snoc half_18_01_φ3 (49890629/1250000000 : ℝ))=(340822213/2000000000 : ℝ)
  rw [alternate_total_snoc,half_18_01_total3]
  norm_num

private theorem half_18_01_bounds4 : ∀ l,0≤half_18_01_φ4 l ∧ half_18_01_φ4 l≤1 ∧
    0≤shiftExponents 18 half_18_01_φ4 l :=
  alternate_bounds_snoc half_18_01_φ3 (49890629/1250000000 : ℝ) half_18_01_bounds3 (by norm_num)

private def half_18_01_φ5 : Fin 5 → ℝ := Fin.snoc half_18_01_φ4 (95466051/2500000000 : ℝ)

private theorem half_18_01_total5 : total half_18_01_φ5=(2085975269/10000000000 : ℝ) := by
  change total (Fin.snoc half_18_01_φ4 (95466051/2500000000 : ℝ))=(2085975269/10000000000 : ℝ)
  rw [alternate_total_snoc,half_18_01_total4]
  norm_num

private theorem half_18_01_bounds5 : ∀ l,0≤half_18_01_φ5 l ∧ half_18_01_φ5 l≤1 ∧
    0≤shiftExponents 18 half_18_01_φ5 l :=
  alternate_bounds_snoc half_18_01_φ4 (95466051/2500000000 : ℝ) half_18_01_bounds4 (by norm_num)

private def half_18_01_φ6 : Fin 6 → ℝ := Fin.snoc half_18_01_φ5 (344168439/10000000000 : ℝ)

private theorem half_18_01_total6 : total half_18_01_φ6=(607535927/2500000000 : ℝ) := by
  change total (Fin.snoc half_18_01_φ5 (344168439/10000000000 : ℝ))=(607535927/2500000000 : ℝ)
  rw [alternate_total_snoc,half_18_01_total5]
  norm_num

private theorem half_18_01_bounds6 : ∀ l,0≤half_18_01_φ6 l ∧ half_18_01_φ6 l≤1 ∧
    0≤shiftExponents 18 half_18_01_φ6 l :=
  alternate_bounds_snoc half_18_01_φ5 (344168439/10000000000 : ℝ) half_18_01_bounds5 (by norm_num)

private def half_18_01_φ7 : Fin 7 → ℝ := Fin.snoc half_18_01_φ6 (225449451/10000000000 : ℝ)

private theorem half_18_01_total7 : total half_18_01_φ7=(2655593159/10000000000 : ℝ) := by
  change total (Fin.snoc half_18_01_φ6 (225449451/10000000000 : ℝ))=(2655593159/10000000000 : ℝ)
  rw [alternate_total_snoc,half_18_01_total6]
  norm_num

private theorem half_18_01_bounds7 : ∀ l,0≤half_18_01_φ7 l ∧ half_18_01_φ7 l≤1 ∧
    0≤shiftExponents 18 half_18_01_φ7 l :=
  alternate_bounds_snoc half_18_01_φ6 (225449451/10000000000 : ℝ) half_18_01_bounds6 (by norm_num)

private theorem half_18_01_prefix : PrefixCondition 18 half_18_01_φ7 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_18_01_φ1, half_18_01_φ2, half_18_01_φ3, half_18_01_φ4, half_18_01_φ5, half_18_01_φ6, half_18_01_φ7, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_18_01_hF2 : SourcePowerBound
    (paddedMoment 18 0 2 128 half_18_01_φ7) (94564748891/10000000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 18) (j := 7) (r := 0) (n := 1) (D := 128)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_18_01_φ7
    (fun i => (half_18_01_bounds7 i).1) (fun i => (half_18_01_bounds7 i).2.1)
    (fun i => (half_18_01_bounds7 i).2.2) half_18_01_prefix
  convert h using 1 <;> norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, half_18_01_total7, parameterExponent, curveLoss, dyadicExponent]

private theorem half_18_01_hx7 : SourcePowerBound
    (powerBoxCross 18 11 128 half_18_01_φ7) (121003780483/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 11) (r := 2) (v := 14) (w := 15) (D := 128)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_18_01_φ7 (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, half_18_01_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, half_18_01_total7, parameterExponent, curveLoss, dyadicExponent]) half_18_01_hF2
    (SeedCompletionHigher18SimpleSeeds.degree18_half_14) (SeedCompletionHigher18SimpleSeeds.degree18_half_15)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, half_18_01_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_01_hx6 : SourcePowerBound
    (powerBoxCross 18 12 64 half_18_01_φ6) (130055410487/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 6) (s := 12) (u := 10) (t := 13)
    (D := 64) (ψ := (225449451/10000000000 : ℝ)) half_18_01_φ6
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_01_bounds6 l).1) (fun l => (half_18_01_bounds6 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, half_18_01_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_11) (SeedCompletionHigher18SimpleSeeds.degree18_half_13)
    (by simpa only [half_18_01_φ7, show (2:ℝ)*64=128 by norm_num] using half_18_01_hx7)
  exact h.weaken (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, half_18_01_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_01_hx5 : SourcePowerBound
    (powerBoxCross 18 13 32 half_18_01_φ5) (142356716973/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 13) (u := 11) (t := 14)
    (D := 32) (ψ := (344168439/10000000000 : ℝ)) half_18_01_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_01_bounds5 l).1) (fun l => (half_18_01_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, half_18_01_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_12) (SeedCompletionHigher18SimpleSeeds.degree18_half_14)
    (by simpa only [half_18_01_φ6, show (2:ℝ)*32=64 by norm_num] using half_18_01_hx6)
  exact h.weaken (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, half_18_01_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_01_hx4 : SourcePowerBound
    (powerBoxCross 18 14 16 half_18_01_φ4) (156797130323/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 14) (u := 12) (t := 15)
    (D := 16) (ψ := (95466051/2500000000 : ℝ)) half_18_01_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_01_bounds4 l).1) (fun l => (half_18_01_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, half_18_01_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_13) (SeedCompletionHigher18SimpleSeeds.degree18_half_15)
    (by simpa only [half_18_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_18_01_hx5)
  exact h.weaken (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, half_18_01_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_01_hx3 : SourcePowerBound
    (powerBoxCross 18 15 8 half_18_01_φ3) (173121687413/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 15) (u := 13) (t := 16)
    (D := 8) (ψ := (49890629/1250000000 : ℝ)) half_18_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_01_bounds3 l).1) (fun l => (half_18_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, half_18_01_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_14) (SeedCompletionHigher18SimpleSeeds.degree18_half_16)
    (by simpa only [half_18_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_18_01_hx4)
  exact h.weaken (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, half_18_01_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_01_hx2 : SourcePowerBound
    (powerBoxCross 18 16 4 half_18_01_φ2) (7652407333/400000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 16) (u := 14) (t := 17)
    (D := 4) (ψ := (16438117/400000000 : ℝ)) half_18_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_01_bounds2 l).1) (fun l => (half_18_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, half_18_01_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_15) (SeedCompletionHigher18SimpleSeeds.degree18_half_17)
    (by simpa only [half_18_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_18_01_hx3)
  exact h.weaken (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, half_18_01_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_01_hx1 : SourcePowerBound
    (powerBoxCross 18 17 2 half_18_01_φ1) (42433325027/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 17) (u := 15) (t := 18)
    (D := 2) (ψ := (421055727/10000000000 : ℝ)) half_18_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_01_bounds1 l).1) (fun l => (half_18_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, half_18_01_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_16) (half_18_00)
    (by simpa only [half_18_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_18_01_hx2)
  exact h.weaken (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, half_18_01_total7, parameterExponent, curveLoss, dyadicExponent])

theorem half_18_01 : AdmissibleExponent 18 36 (56943719677/2500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 16) (ψ := (472977381/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (SeedCompletionHigher18SimpleSeeds.degree18_half_17)
    (by simpa only [half_18_01_φ1] using half_18_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, half_18_01_total7, parameterExponent, curveLoss, dyadicExponent])

theorem chord_1 : AdmissibleExponent 18 38 (491089089619/20000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 38) (t := (3/4 : ℝ))
    (half_18_01) (half_22_00)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_19_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (480845729/10000000000 : ℝ)

private theorem half_19_01_total1 : total half_19_01_φ1=(480845729/10000000000 : ℝ) := by
  norm_num [half_19_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_19_01_bounds1 : ∀ l,0≤half_19_01_φ1 l ∧ half_19_01_φ1 l≤1 ∧
    0≤shiftExponents 18 half_19_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (480845729/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_19_01_φ2 : Fin 2 → ℝ := Fin.snoc half_19_01_φ1 (22178039/500000000 : ℝ)

private theorem half_19_01_total2 : total half_19_01_φ2=(924406509/10000000000 : ℝ) := by
  change total (Fin.snoc half_19_01_φ1 (22178039/500000000 : ℝ))=(924406509/10000000000 : ℝ)
  rw [alternate_total_snoc,half_19_01_total1]
  norm_num

private theorem half_19_01_bounds2 : ∀ l,0≤half_19_01_φ2 l ∧ half_19_01_φ2 l≤1 ∧
    0≤shiftExponents 18 half_19_01_φ2 l :=
  alternate_bounds_snoc half_19_01_φ1 (22178039/500000000 : ℝ) half_19_01_bounds1 (by norm_num)

private def half_19_01_φ3 : Fin 3 → ℝ := Fin.snoc half_19_01_φ2 (105042519/2500000000 : ℝ)

private theorem half_19_01_total3 : total half_19_01_φ3=(268915317/2000000000 : ℝ) := by
  change total (Fin.snoc half_19_01_φ2 (105042519/2500000000 : ℝ))=(268915317/2000000000 : ℝ)
  rw [alternate_total_snoc,half_19_01_total2]
  norm_num

private theorem half_19_01_bounds3 : ∀ l,0≤half_19_01_φ3 l ∧ half_19_01_φ3 l≤1 ∧
    0≤shiftExponents 18 half_19_01_φ3 l :=
  alternate_bounds_snoc half_19_01_φ2 (105042519/2500000000 : ℝ) half_19_01_bounds2 (by norm_num)

private def half_19_01_φ4 : Fin 4 → ℝ := Fin.snoc half_19_01_φ3 (25592693/625000000 : ℝ)

private theorem half_19_01_total4 : total half_19_01_φ4=(1754059673/10000000000 : ℝ) := by
  change total (Fin.snoc half_19_01_φ3 (25592693/625000000 : ℝ))=(1754059673/10000000000 : ℝ)
  rw [alternate_total_snoc,half_19_01_total3]
  norm_num

private theorem half_19_01_bounds4 : ∀ l,0≤half_19_01_φ4 l ∧ half_19_01_φ4 l≤1 ∧
    0≤shiftExponents 18 half_19_01_φ4 l :=
  alternate_bounds_snoc half_19_01_φ3 (25592693/625000000 : ℝ) half_19_01_bounds3 (by norm_num)

private def half_19_01_φ5 : Fin 5 → ℝ := Fin.snoc half_19_01_φ4 (395748897/10000000000 : ℝ)

private theorem half_19_01_total5 : total half_19_01_φ5=(214980857/1000000000 : ℝ) := by
  change total (Fin.snoc half_19_01_φ4 (395748897/10000000000 : ℝ))=(214980857/1000000000 : ℝ)
  rw [alternate_total_snoc,half_19_01_total4]
  norm_num

private theorem half_19_01_bounds5 : ∀ l,0≤half_19_01_φ5 l ∧ half_19_01_φ5 l≤1 ∧
    0≤shiftExponents 18 half_19_01_φ5 l :=
  alternate_bounds_snoc half_19_01_φ4 (395748897/10000000000 : ℝ) half_19_01_bounds4 (by norm_num)

private def half_19_01_φ6 : Fin 6 → ℝ := Fin.snoc half_19_01_φ5 (185953263/5000000000 : ℝ)

private theorem half_19_01_total6 : total half_19_01_φ6=(315214387/1250000000 : ℝ) := by
  change total (Fin.snoc half_19_01_φ5 (185953263/5000000000 : ℝ))=(315214387/1250000000 : ℝ)
  rw [alternate_total_snoc,half_19_01_total5]
  norm_num

private theorem half_19_01_bounds6 : ∀ l,0≤half_19_01_φ6 l ∧ half_19_01_φ6 l≤1 ∧
    0≤shiftExponents 18 half_19_01_φ6 l :=
  alternate_bounds_snoc half_19_01_φ5 (185953263/5000000000 : ℝ) half_19_01_bounds5 (by norm_num)

private def half_19_01_φ7 : Fin 7 → ℝ := Fin.snoc half_19_01_φ6 (310162599/10000000000 : ℝ)

private theorem half_19_01_total7 : total half_19_01_φ7=(566375539/2000000000 : ℝ) := by
  change total (Fin.snoc half_19_01_φ6 (310162599/10000000000 : ℝ))=(566375539/2000000000 : ℝ)
  rw [alternate_total_snoc,half_19_01_total6]
  norm_num

private theorem half_19_01_bounds7 : ∀ l,0≤half_19_01_φ7 l ∧ half_19_01_φ7 l≤1 ∧
    0≤shiftExponents 18 half_19_01_φ7 l :=
  alternate_bounds_snoc half_19_01_φ6 (310162599/10000000000 : ℝ) half_19_01_bounds6 (by norm_num)

private theorem half_19_01_prefix : PrefixCondition 18 half_19_01_φ7 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_19_01_φ1, half_19_01_φ2, half_19_01_φ3, half_19_01_φ4, half_19_01_φ5, half_19_01_φ6, half_19_01_φ7, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_19_01_hF2 : SourcePowerBound
    (paddedMoment 18 0 2 128 half_19_01_φ7) (17114847511/2000000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 18) (j := 7) (r := 0) (n := 1) (D := 128)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_19_01_φ7
    (fun i => (half_19_01_bounds7 i).1) (fun i => (half_19_01_bounds7 i).2.1)
    (fun i => (half_19_01_bounds7 i).2.2) half_19_01_prefix
  convert h using 1 <;> norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, half_19_01_total7, parameterExponent, curveLoss, dyadicExponent]

private theorem half_19_01_hx7 : SourcePowerBound
    (powerBoxCross 18 12 128 half_19_01_φ7) (127032282121/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 12) (r := 2) (v := 0) (w := 16) (D := 128)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_19_01_φ7 (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, half_19_01_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, half_19_01_total7, parameterExponent, curveLoss, dyadicExponent]) half_19_01_hF2
    (admissibleExponent_zero 18) (SeedCompletionHigher18SimpleSeeds.degree18_half_16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, half_19_01_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_01_hx6 : SourcePowerBound
    (powerBoxCross 18 13 64 half_19_01_φ6) (17263847711/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 6) (s := 13) (u := 11) (t := 14)
    (D := 64) (ψ := (310162599/10000000000 : ℝ)) half_19_01_φ6
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_01_bounds6 l).1) (fun l => (half_19_01_bounds6 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, half_19_01_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_12) (SeedCompletionHigher18SimpleSeeds.degree18_half_14)
    (by simpa only [half_19_01_φ7, show (2:ℝ)*64=128 by norm_num] using half_19_01_hx7)
  exact h.weaken (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, half_19_01_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_01_hx5 : SourcePowerBound
    (powerBoxCross 18 14 32 half_19_01_φ5) (75857064269/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 14) (u := 12) (t := 15)
    (D := 32) (ψ := (185953263/5000000000 : ℝ)) half_19_01_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_01_bounds5 l).1) (fun l => (half_19_01_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, half_19_01_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_13) (SeedCompletionHigher18SimpleSeeds.degree18_half_15)
    (by simpa only [half_19_01_φ6, show (2:ℝ)*32=64 by norm_num] using half_19_01_hx6)
  exact h.weaken (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, half_19_01_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_01_hx4 : SourcePowerBound
    (powerBoxCross 18 15 16 half_19_01_φ4) (167305396047/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 15) (u := 13) (t := 16)
    (D := 16) (ψ := (395748897/10000000000 : ℝ)) half_19_01_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_01_bounds4 l).1) (fun l => (half_19_01_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, half_19_01_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_14) (SeedCompletionHigher18SimpleSeeds.degree18_half_16)
    (by simpa only [half_19_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_19_01_hx5)
  exact h.weaken (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, half_19_01_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_01_hx3 : SourcePowerBound
    (powerBoxCross 18 16 8 half_19_01_φ3) (36956389437/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 16) (u := 14) (t := 17)
    (D := 8) (ψ := (25592693/625000000 : ℝ)) half_19_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_01_bounds3 l).1) (fun l => (half_19_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, half_19_01_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_15) (SeedCompletionHigher18SimpleSeeds.degree18_half_17)
    (by simpa only [half_19_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_19_01_hx4)
  exact h.weaken (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, half_19_01_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_01_hx2 : SourcePowerBound
    (powerBoxCross 18 17 4 half_19_01_φ2) (8176230591/400000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 17) (u := 15) (t := 18)
    (D := 4) (ψ := (105042519/2500000000 : ℝ)) half_19_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_01_bounds2 l).1) (fun l => (half_19_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, half_19_01_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_16) (half_18_01)
    (by simpa only [half_19_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_19_01_hx3)
  exact h.weaken (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, half_19_01_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_01_hx1 : SourcePowerBound
    (powerBoxCross 18 18 2 half_19_01_φ1) (56825816671/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 18) (u := 16) (t := 19)
    (D := 2) (ψ := (22178039/500000000 : ℝ)) half_19_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_01_bounds1 l).1) (fun l => (half_19_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, half_19_01_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_17) (chord_1)
    (by simpa only [half_19_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_19_01_hx2)
  exact h.weaken (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, half_19_01_total7, parameterExponent, curveLoss, dyadicExponent])

theorem half_19_01 : AdmissibleExponent 18 38 (244132867199/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 17) (ψ := (480845729/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_18_01)
    (by simpa only [half_19_01_φ1] using half_19_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, half_19_01_total7, parameterExponent, curveLoss, dyadicExponent])

theorem chord_4 : AdmissibleExponent 18 40 (524465127163/20000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 40) (t := (5/6 : ℝ))
    (half_19_01) (half_25_00)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_20_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (9727579/200000000 : ℝ)

private theorem half_20_01_total1 : total half_20_01_φ1=(9727579/200000000 : ℝ) := by
  norm_num [half_20_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_20_01_bounds1 : ∀ l,0≤half_20_01_φ1 l ∧ half_20_01_φ1 l≤1 ∧
    0≤shiftExponents 18 half_20_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (9727579/200000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_20_01_φ2 : Fin 2 → ℝ := Fin.snoc half_20_01_φ1 (442627487/10000000000 : ℝ)

private theorem half_20_01_total2 : total half_20_01_φ2=(929006437/10000000000 : ℝ) := by
  change total (Fin.snoc half_20_01_φ1 (442627487/10000000000 : ℝ))=(929006437/10000000000 : ℝ)
  rw [alternate_total_snoc,half_20_01_total1]
  norm_num

private theorem half_20_01_bounds2 : ∀ l,0≤half_20_01_φ2 l ∧ half_20_01_φ2 l≤1 ∧
    0≤shiftExponents 18 half_20_01_φ2 l :=
  alternate_bounds_snoc half_20_01_φ1 (442627487/10000000000 : ℝ) half_20_01_bounds1 (by norm_num)

private def half_20_01_φ3 : Fin 3 → ℝ := Fin.snoc half_20_01_φ2 (442074989/10000000000 : ℝ)

private theorem half_20_01_total3 : total half_20_01_φ3=(685540713/5000000000 : ℝ) := by
  change total (Fin.snoc half_20_01_φ2 (442074989/10000000000 : ℝ))=(685540713/5000000000 : ℝ)
  rw [alternate_total_snoc,half_20_01_total2]
  norm_num

private theorem half_20_01_bounds3 : ∀ l,0≤half_20_01_φ3 l ∧ half_20_01_φ3 l≤1 ∧
    0≤shiftExponents 18 half_20_01_φ3 l :=
  alternate_bounds_snoc half_20_01_φ2 (442074989/10000000000 : ℝ) half_20_01_bounds2 (by norm_num)

private def half_20_01_φ4 : Fin 4 → ℝ := Fin.snoc half_20_01_φ3 (26183963/625000000 : ℝ)

private theorem half_20_01_total4 : total half_20_01_φ4=(895012417/5000000000 : ℝ) := by
  change total (Fin.snoc half_20_01_φ3 (26183963/625000000 : ℝ))=(895012417/5000000000 : ℝ)
  rw [alternate_total_snoc,half_20_01_total3]
  norm_num

private theorem half_20_01_bounds4 : ∀ l,0≤half_20_01_φ4 l ∧ half_20_01_φ4 l≤1 ∧
    0≤shiftExponents 18 half_20_01_φ4 l :=
  alternate_bounds_snoc half_20_01_φ3 (26183963/625000000 : ℝ) half_20_01_bounds3 (by norm_num)

private def half_20_01_φ5 : Fin 5 → ℝ := Fin.snoc half_20_01_φ4 (406962461/10000000000 : ℝ)

private theorem half_20_01_total5 : total half_20_01_φ5=(439397459/2000000000 : ℝ) := by
  change total (Fin.snoc half_20_01_φ4 (406962461/10000000000 : ℝ))=(439397459/2000000000 : ℝ)
  rw [alternate_total_snoc,half_20_01_total4]
  norm_num

private theorem half_20_01_bounds5 : ∀ l,0≤half_20_01_φ5 l ∧ half_20_01_φ5 l≤1 ∧
    0≤shiftExponents 18 half_20_01_φ5 l :=
  alternate_bounds_snoc half_20_01_φ4 (406962461/10000000000 : ℝ) half_20_01_bounds4 (by norm_num)

private def half_20_01_φ6 : Fin 6 → ℝ := Fin.snoc half_20_01_φ5 (15560229/400000000 : ℝ)

private theorem half_20_01_total6 : total half_20_01_φ6=(129299651/500000000 : ℝ) := by
  change total (Fin.snoc half_20_01_φ5 (15560229/400000000 : ℝ))=(129299651/500000000 : ℝ)
  rw [alternate_total_snoc,half_20_01_total5]
  norm_num

private theorem half_20_01_bounds6 : ∀ l,0≤half_20_01_φ6 l ∧ half_20_01_φ6 l≤1 ∧
    0≤shiftExponents 18 half_20_01_φ6 l :=
  alternate_bounds_snoc half_20_01_φ5 (15560229/400000000 : ℝ) half_20_01_bounds5 (by norm_num)

private def half_20_01_φ7 : Fin 7 → ℝ := Fin.snoc half_20_01_φ6 (175304833/5000000000 : ℝ)

private theorem half_20_01_total7 : total half_20_01_φ7=(1468301343/5000000000 : ℝ) := by
  change total (Fin.snoc half_20_01_φ6 (175304833/5000000000 : ℝ))=(1468301343/5000000000 : ℝ)
  rw [alternate_total_snoc,half_20_01_total6]
  norm_num

private theorem half_20_01_bounds7 : ∀ l,0≤half_20_01_φ7 l ∧ half_20_01_φ7 l≤1 ∧
    0≤shiftExponents 18 half_20_01_φ7 l :=
  alternate_bounds_snoc half_20_01_φ6 (175304833/5000000000 : ℝ) half_20_01_bounds6 (by norm_num)

private def half_20_01_φ8 : Fin 8 → ℝ := Fin.snoc half_20_01_φ7 (58923811/2500000000 : ℝ)

private theorem half_20_01_total8 : total half_20_01_φ8=(317229793/1000000000 : ℝ) := by
  change total (Fin.snoc half_20_01_φ7 (58923811/2500000000 : ℝ))=(317229793/1000000000 : ℝ)
  rw [alternate_total_snoc,half_20_01_total7]
  norm_num

private theorem half_20_01_bounds8 : ∀ l,0≤half_20_01_φ8 l ∧ half_20_01_φ8 l≤1 ∧
    0≤shiftExponents 18 half_20_01_φ8 l :=
  alternate_bounds_snoc half_20_01_φ7 (58923811/2500000000 : ℝ) half_20_01_bounds7 (by norm_num)

private theorem half_20_01_prefix : PrefixCondition 18 half_20_01_φ8 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_20_01_φ1, half_20_01_φ2, half_20_01_φ3, half_20_01_φ4, half_20_01_φ5, half_20_01_φ6, half_20_01_φ7, half_20_01_φ8, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_20_01_hF2 : SourcePowerBound
    (paddedMoment 18 0 2 256 half_20_01_φ8) (9821280557/1000000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 18) (j := 8) (r := 0) (n := 1) (D := 256)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_20_01_φ8
    (fun i => (half_20_01_bounds8 i).1) (fun i => (half_20_01_bounds8 i).2.1)
    (fun i => (half_20_01_bounds8 i).2.2) half_20_01_prefix
  convert h using 1 <;> norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, half_20_01_total7, half_20_01_total8, parameterExponent, curveLoss, dyadicExponent]

private theorem half_20_01_hx8 : SourcePowerBound
    (powerBoxCross 18 12 256 half_20_01_φ8) (25035010237/2000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 12) (r := 2) (v := 0) (w := 16) (D := 256)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_20_01_φ8 (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, half_20_01_total7, half_20_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, half_20_01_total7, half_20_01_total8, parameterExponent, curveLoss, dyadicExponent]) half_20_01_hF2
    (admissibleExponent_zero 18) (SeedCompletionHigher18SimpleSeeds.degree18_half_16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, half_20_01_total7, half_20_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_01_hx7 : SourcePowerBound
    (powerBoxCross 18 13 128 half_20_01_φ7) (134333899949/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 7) (s := 13) (u := 11) (t := 14)
    (D := 128) (ψ := (58923811/2500000000 : ℝ)) half_20_01_φ7
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_01_bounds7 l).1) (fun l => (half_20_01_bounds7 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, half_20_01_total7, half_20_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_12) (SeedCompletionHigher18SimpleSeeds.degree18_half_14)
    (by simpa only [half_20_01_φ8, show (2:ℝ)*128=256 by norm_num] using half_20_01_hx8)
  exact h.weaken (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, half_20_01_total7, half_20_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_01_hx6 : SourcePowerBound
    (powerBoxCross 18 14 64 half_20_01_φ6) (146891157549/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 6) (s := 14) (u := 12) (t := 15)
    (D := 64) (ψ := (175304833/5000000000 : ℝ)) half_20_01_φ6
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_01_bounds6 l).1) (fun l => (half_20_01_bounds6 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, half_20_01_total7, half_20_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_13) (SeedCompletionHigher18SimpleSeeds.degree18_half_15)
    (by simpa only [half_20_01_φ7, show (2:ℝ)*64=128 by norm_num] using half_20_01_hx7)
  exact h.weaken (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, half_20_01_total7, half_20_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_01_hx5 : SourcePowerBound
    (powerBoxCross 18 15 32 half_20_01_φ5) (80843145007/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 15) (u := 13) (t := 16)
    (D := 32) (ψ := (15560229/400000000 : ℝ)) half_20_01_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_01_bounds5 l).1) (fun l => (half_20_01_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, half_20_01_total7, half_20_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_14) (SeedCompletionHigher18SimpleSeeds.degree18_half_16)
    (by simpa only [half_20_01_φ6, show (2:ℝ)*32=64 by norm_num] using half_20_01_hx6)
  exact h.weaken (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, half_20_01_total7, half_20_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_01_hx4 : SourcePowerBound
    (powerBoxCross 18 16 16 half_20_01_φ4) (89217155721/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 16) (u := 14) (t := 17)
    (D := 16) (ψ := (406962461/10000000000 : ℝ)) half_20_01_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_01_bounds4 l).1) (fun l => (half_20_01_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, half_20_01_total7, half_20_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_15) (SeedCompletionHigher18SimpleSeeds.degree18_half_17)
    (by simpa only [half_20_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_20_01_hx5)
  exact h.weaken (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, half_20_01_total7, half_20_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_01_hx3 : SourcePowerBound
    (powerBoxCross 18 17 8 half_20_01_φ3) (197329130503/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 17) (u := 15) (t := 18)
    (D := 8) (ψ := (26183963/625000000 : ℝ)) half_20_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_01_bounds3 l).1) (fun l => (half_20_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, half_20_01_total7, half_20_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_16) (half_18_01)
    (by simpa only [half_20_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_20_01_hx4)
  exact h.weaken (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, half_20_01_total7, half_20_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_01_hx2 : SourcePowerBound
    (powerBoxCross 18 18 4 half_20_01_φ2) (273485789/12500000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 18) (u := 16) (t := 19)
    (D := 4) (ψ := (442074989/10000000000 : ℝ)) half_20_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_01_bounds2 l).1) (fun l => (half_20_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, half_20_01_total7, half_20_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_17) (half_19_01)
    (by simpa only [half_20_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_20_01_hx3)
  exact h.weaken (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, half_20_01_total7, half_20_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_01_hx1 : SourcePowerBound
    (powerBoxCross 18 19 2 half_20_01_φ1) (15171571087/625000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 19) (u := 17) (t := 20)
    (D := 2) (ψ := (442627487/10000000000 : ℝ)) half_20_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_01_bounds1 l).1) (fun l => (half_20_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, half_20_01_total7, half_20_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_01) (chord_4)
    (by simpa only [half_20_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_20_01_hx2)
  exact h.weaken (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, half_20_01_total7, half_20_01_total8, parameterExponent, curveLoss, dyadicExponent])

theorem half_20_01 : AdmissibleExponent 18 40 (130370579271/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 18) (ψ := (9727579/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_19_01)
    (by simpa only [half_20_01_φ1] using half_20_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, half_20_01_total7, half_20_01_total8, parameterExponent, curveLoss, dyadicExponent])

theorem chord_9 : AdmissibleExponent 18 42 (1953642235659/70000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 42) (t := (6/7 : ℝ))
    (half_20_01) (half_27_00)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_21_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (246116339/5000000000 : ℝ)

private theorem half_21_01_total1 : total half_21_01_φ1=(246116339/5000000000 : ℝ) := by
  norm_num [half_21_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_21_01_bounds1 : ∀ l,0≤half_21_01_φ1 l ∧ half_21_01_φ1 l≤1 ∧
    0≤shiftExponents 18 half_21_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (246116339/5000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_21_01_φ2 : Fin 2 → ℝ := Fin.snoc half_21_01_φ1 (446306611/10000000000 : ℝ)

private theorem half_21_01_total2 : total half_21_01_φ2=(938539289/10000000000 : ℝ) := by
  change total (Fin.snoc half_21_01_φ1 (446306611/10000000000 : ℝ))=(938539289/10000000000 : ℝ)
  rw [alternate_total_snoc,half_21_01_total1]
  norm_num

private theorem half_21_01_bounds2 : ∀ l,0≤half_21_01_φ2 l ∧ half_21_01_φ2 l≤1 ∧
    0≤shiftExponents 18 half_21_01_φ2 l :=
  alternate_bounds_snoc half_21_01_φ1 (446306611/10000000000 : ℝ) half_21_01_bounds1 (by norm_num)

private def half_21_01_φ3 : Fin 3 → ℝ := Fin.snoc half_21_01_φ2 (220844081/5000000000 : ℝ)

private theorem half_21_01_total3 : total half_21_01_φ3=(1380227451/10000000000 : ℝ) := by
  change total (Fin.snoc half_21_01_φ2 (220844081/5000000000 : ℝ))=(1380227451/10000000000 : ℝ)
  rw [alternate_total_snoc,half_21_01_total2]
  norm_num

private theorem half_21_01_bounds3 : ∀ l,0≤half_21_01_φ3 l ∧ half_21_01_φ3 l≤1 ∧
    0≤shiftExponents 18 half_21_01_φ3 l :=
  alternate_bounds_snoc half_21_01_φ2 (220844081/5000000000 : ℝ) half_21_01_bounds2 (by norm_num)

private def half_21_01_φ4 : Fin 4 → ℝ := Fin.snoc half_21_01_φ3 (440459189/10000000000 : ℝ)

private theorem half_21_01_total4 : total half_21_01_φ4=(22758583/125000000 : ℝ) := by
  change total (Fin.snoc half_21_01_φ3 (440459189/10000000000 : ℝ))=(22758583/125000000 : ℝ)
  rw [alternate_total_snoc,half_21_01_total3]
  norm_num

private theorem half_21_01_bounds4 : ∀ l,0≤half_21_01_φ4 l ∧ half_21_01_φ4 l≤1 ∧
    0≤shiftExponents 18 half_21_01_φ4 l :=
  alternate_bounds_snoc half_21_01_φ3 (440459189/10000000000 : ℝ) half_21_01_bounds3 (by norm_num)

private def half_21_01_φ5 : Fin 5 → ℝ := Fin.snoc half_21_01_φ4 (417358139/10000000000 : ℝ)

private theorem half_21_01_total5 : total half_21_01_φ5=(2238044779/10000000000 : ℝ) := by
  change total (Fin.snoc half_21_01_φ4 (417358139/10000000000 : ℝ))=(2238044779/10000000000 : ℝ)
  rw [alternate_total_snoc,half_21_01_total4]
  norm_num

private theorem half_21_01_bounds5 : ∀ l,0≤half_21_01_φ5 l ∧ half_21_01_φ5 l≤1 ∧
    0≤shiftExponents 18 half_21_01_φ5 l :=
  alternate_bounds_snoc half_21_01_φ4 (417358139/10000000000 : ℝ) half_21_01_bounds4 (by norm_num)

private def half_21_01_φ6 : Fin 6 → ℝ := Fin.snoc half_21_01_φ5 (50419799/1250000000 : ℝ)

private theorem half_21_01_total6 : total half_21_01_φ6=(2641403171/10000000000 : ℝ) := by
  change total (Fin.snoc half_21_01_φ5 (50419799/1250000000 : ℝ))=(2641403171/10000000000 : ℝ)
  rw [alternate_total_snoc,half_21_01_total5]
  norm_num

private theorem half_21_01_bounds6 : ∀ l,0≤half_21_01_φ6 l ∧ half_21_01_φ6 l≤1 ∧
    0≤shiftExponents 18 half_21_01_φ6 l :=
  alternate_bounds_snoc half_21_01_φ5 (50419799/1250000000 : ℝ) half_21_01_bounds5 (by norm_num)

private def half_21_01_φ7 : Fin 7 → ℝ := Fin.snoc half_21_01_φ6 (378813693/10000000000 : ℝ)

private theorem half_21_01_total7 : total half_21_01_φ7=(94381777/312500000 : ℝ) := by
  change total (Fin.snoc half_21_01_φ6 (378813693/10000000000 : ℝ))=(94381777/312500000 : ℝ)
  rw [alternate_total_snoc,half_21_01_total6]
  norm_num

private theorem half_21_01_bounds7 : ∀ l,0≤half_21_01_φ7 l ∧ half_21_01_φ7 l≤1 ∧
    0≤shiftExponents 18 half_21_01_φ7 l :=
  alternate_bounds_snoc half_21_01_φ6 (378813693/10000000000 : ℝ) half_21_01_bounds6 (by norm_num)

private def half_21_01_φ8 : Fin 8 → ℝ := Fin.snoc half_21_01_φ7 (317722211/10000000000 : ℝ)

private theorem half_21_01_total8 : total half_21_01_φ8=(133517563/400000000 : ℝ) := by
  change total (Fin.snoc half_21_01_φ7 (317722211/10000000000 : ℝ))=(133517563/400000000 : ℝ)
  rw [alternate_total_snoc,half_21_01_total7]
  norm_num

private theorem half_21_01_bounds8 : ∀ l,0≤half_21_01_φ8 l ∧ half_21_01_φ8 l≤1 ∧
    0≤shiftExponents 18 half_21_01_φ8 l :=
  alternate_bounds_snoc half_21_01_φ7 (317722211/10000000000 : ℝ) half_21_01_bounds7 (by norm_num)

private theorem half_21_01_prefix : PrefixCondition 18 half_21_01_φ8 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_21_01_φ1, half_21_01_φ2, half_21_01_φ3, half_21_01_φ4, half_21_01_φ5, half_21_01_φ6, half_21_01_φ7, half_21_01_φ8, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_21_01_hF4 : SourcePowerBound
    (paddedMoment 18 0 4 256 half_21_01_φ8) (12767391349/600000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 18) (j := 8) (r := 0) (n := 2) (D := 256)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_21_01_φ8
    (fun i => (half_21_01_bounds8 i).1) (fun i => (half_21_01_bounds8 i).2.1)
    (fun i => (half_21_01_bounds8 i).2.2) half_21_01_prefix
  convert h using 1 <;> norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, parameterExponent, curveLoss, dyadicExponent]

private theorem half_21_01_hF2 : SourcePowerBound
    (paddedMoment 18 0 2 256 half_21_01_φ8) (215447311/24000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 18) (j := 8) (r := 0) (n := 1) (D := 256)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_21_01_φ8
    (fun i => (half_21_01_bounds8 i).1) (fun i => (half_21_01_bounds8 i).2.1)
    (fun i => (half_21_01_bounds8 i).2.2) half_21_01_prefix
  convert h using 1 <;> norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, parameterExponent, curveLoss, dyadicExponent]

private theorem half_21_01_hx8 : SourcePowerBound
    (powerBoxCross 18 13 256 half_21_01_φ8) (130785851827/10000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 13) (r := 2) (v := 4) (t := 17) (D := 256)
    (a := (15/68 : ℝ)) (b := (1/68 : ℝ)) (c := (13/17 : ℝ))
    (by norm_num) half_21_01_φ8 (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, parameterExponent, curveLoss, dyadicExponent]) half_21_01_hF2 half_21_01_hF4
    (SeedCompletionHigher18SimpleSeeds.degree18_half_17)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_01_hx7 : SourcePowerBound
    (powerBoxCross 18 14 128 half_21_01_φ7) (14207218927/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 7) (s := 14) (u := 12) (t := 15)
    (D := 128) (ψ := (317722211/10000000000 : ℝ)) half_21_01_φ7
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_01_bounds7 l).1) (fun l => (half_21_01_bounds7 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_13) (SeedCompletionHigher18SimpleSeeds.degree18_half_15)
    (by simpa only [half_21_01_φ8, show (2:ℝ)*128=256 by norm_num] using half_21_01_hx8)
  exact h.weaken (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_01_hx6 : SourcePowerBound
    (powerBoxCross 18 15 64 half_21_01_φ6) (77997676839/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 6) (s := 15) (u := 13) (t := 16)
    (D := 64) (ψ := (378813693/10000000000 : ℝ)) half_21_01_φ6
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_01_bounds6 l).1) (fun l => (half_21_01_bounds6 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_14) (SeedCompletionHigher18SimpleSeeds.degree18_half_16)
    (by simpa only [half_21_01_φ7, show (2:ℝ)*64=128 by norm_num] using half_21_01_hx7)
  exact h.weaken (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_01_hx5 : SourcePowerBound
    (powerBoxCross 18 16 32 half_21_01_φ5) (171985968933/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 16) (u := 14) (t := 17)
    (D := 32) (ψ := (50419799/1250000000 : ℝ)) half_21_01_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_01_bounds5 l).1) (fun l => (half_21_01_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_15) (SeedCompletionHigher18SimpleSeeds.degree18_half_17)
    (by simpa only [half_21_01_φ6, show (2:ℝ)*32=64 by norm_num] using half_21_01_hx6)
  exact h.weaken (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_01_hx4 : SourcePowerBound
    (powerBoxCross 18 17 16 half_21_01_φ4) (95069152303/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 17) (u := 15) (t := 18)
    (D := 16) (ψ := (417358139/10000000000 : ℝ)) half_21_01_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_01_bounds4 l).1) (fun l => (half_21_01_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_16) (half_18_01)
    (by simpa only [half_21_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_21_01_hx5)
  exact h.weaken (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_01_hx3 : SourcePowerBound
    (powerBoxCross 18 18 8 half_21_01_φ3) (105411642469/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 18) (u := 16) (t := 19)
    (D := 8) (ψ := (440459189/10000000000 : ℝ)) half_21_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_01_bounds3 l).1) (fun l => (half_21_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_17) (half_19_01)
    (by simpa only [half_21_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_21_01_hx4)
  exact h.weaken (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_01_hx2 : SourcePowerBound
    (powerBoxCross 18 19 4 half_21_01_φ2) (233298389541/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 19) (u := 17) (t := 20)
    (D := 4) (ψ := (220844081/5000000000 : ℝ)) half_21_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_01_bounds2 l).1) (fun l => (half_21_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_01) (half_20_01)
    (by simpa only [half_21_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_21_01_hx3)
  exact h.weaken (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_01_hx1 : SourcePowerBound
    (powerBoxCross 18 20 2 half_21_01_φ1) (129199429681/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 20) (u := 18) (t := 21)
    (D := 2) (ψ := (446306611/10000000000 : ℝ)) half_21_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_01_bounds1 l).1) (fun l => (half_21_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_19_01) (chord_9)
    (by simpa only [half_21_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_21_01_hx2)
  exact h.weaken (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, parameterExponent, curveLoss, dyadicExponent])

theorem half_21_01 : AdmissibleExponent 18 42 (69398983451/2500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 19) (ψ := (246116339/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_20_01)
    (by simpa only [half_21_01_φ1] using half_21_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, half_21_01_total7, half_21_01_total8, parameterExponent, curveLoss, dyadicExponent])

theorem chord_15 : AdmissibleExponent 18 44 (888454064921/30000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 44) (t := (8/9 : ℝ))
    (half_21_01) (half_30_00)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_22_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (9951439/200000000 : ℝ)

private theorem half_22_01_total1 : total half_22_01_φ1=(9951439/200000000 : ℝ) := by
  norm_num [half_22_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_22_01_bounds1 : ∀ l,0≤half_22_01_φ1 l ∧ half_22_01_φ1 l≤1 ∧
    0≤shiftExponents 18 half_22_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (9951439/200000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_22_01_φ2 : Fin 2 → ℝ := Fin.snoc half_22_01_φ1 (90429643/2000000000 : ℝ)

private theorem half_22_01_total2 : total half_22_01_φ2=(189944033/2000000000 : ℝ) := by
  change total (Fin.snoc half_22_01_φ1 (90429643/2000000000 : ℝ))=(189944033/2000000000 : ℝ)
  rw [alternate_total_snoc,half_22_01_total1]
  norm_num

private theorem half_22_01_bounds2 : ∀ l,0≤half_22_01_φ2 l ∧ half_22_01_φ2 l≤1 ∧
    0≤shiftExponents 18 half_22_01_φ2 l :=
  alternate_bounds_snoc half_22_01_φ1 (90429643/2000000000 : ℝ) half_22_01_bounds1 (by norm_num)

private def half_22_01_φ3 : Fin 3 → ℝ := Fin.snoc half_22_01_φ2 (22280079/500000000 : ℝ)

private theorem half_22_01_total3 : total half_22_01_φ3=(279064349/2000000000 : ℝ) := by
  change total (Fin.snoc half_22_01_φ2 (22280079/500000000 : ℝ))=(279064349/2000000000 : ℝ)
  rw [alternate_total_snoc,half_22_01_total2]
  norm_num

private theorem half_22_01_bounds3 : ∀ l,0≤half_22_01_φ3 l ∧ half_22_01_φ3 l≤1 ∧
    0≤shiftExponents 18 half_22_01_φ3 l :=
  alternate_bounds_snoc half_22_01_φ2 (22280079/500000000 : ℝ) half_22_01_bounds2 (by norm_num)

private def half_22_01_φ4 : Fin 4 → ℝ := Fin.snoc half_22_01_φ3 (88126663/2000000000 : ℝ)

private theorem half_22_01_total4 : total half_22_01_φ4=(91797753/500000000 : ℝ) := by
  change total (Fin.snoc half_22_01_φ3 (88126663/2000000000 : ℝ))=(91797753/500000000 : ℝ)
  rw [alternate_total_snoc,half_22_01_total3]
  norm_num

private theorem half_22_01_bounds4 : ∀ l,0≤half_22_01_φ4 l ∧ half_22_01_φ4 l≤1 ∧
    0≤shiftExponents 18 half_22_01_φ4 l :=
  alternate_bounds_snoc half_22_01_φ3 (88126663/2000000000 : ℝ) half_22_01_bounds3 (by norm_num)

private def half_22_01_φ5 : Fin 5 → ℝ := Fin.snoc half_22_01_φ4 (87705883/2000000000 : ℝ)

private theorem half_22_01_total5 : total half_22_01_φ5=(90979379/400000000 : ℝ) := by
  change total (Fin.snoc half_22_01_φ4 (87705883/2000000000 : ℝ))=(90979379/400000000 : ℝ)
  rw [alternate_total_snoc,half_22_01_total4]
  norm_num

private theorem half_22_01_bounds5 : ∀ l,0≤half_22_01_φ5 l ∧ half_22_01_φ5 l≤1 ∧
    0≤shiftExponents 18 half_22_01_φ5 l :=
  alternate_bounds_snoc half_22_01_φ4 (87705883/2000000000 : ℝ) half_22_01_bounds4 (by norm_num)

private def half_22_01_φ6 : Fin 6 → ℝ := Fin.snoc half_22_01_φ5 (414886801/10000000000 : ℝ)

private theorem half_22_01_total6 : total half_22_01_φ6=(672342819/2500000000 : ℝ) := by
  change total (Fin.snoc half_22_01_φ5 (414886801/10000000000 : ℝ))=(672342819/2500000000 : ℝ)
  rw [alternate_total_snoc,half_22_01_total5]
  norm_num

private theorem half_22_01_bounds6 : ∀ l,0≤half_22_01_φ6 l ∧ half_22_01_φ6 l≤1 ∧
    0≤shiftExponents 18 half_22_01_φ6 l :=
  alternate_bounds_snoc half_22_01_φ5 (414886801/10000000000 : ℝ) half_22_01_bounds5 (by norm_num)

private def half_22_01_φ7 : Fin 7 → ℝ := Fin.snoc half_22_01_φ6 (49633621/1250000000 : ℝ)

private theorem half_22_01_total7 : total half_22_01_φ7=(771610061/2500000000 : ℝ) := by
  change total (Fin.snoc half_22_01_φ6 (49633621/1250000000 : ℝ))=(771610061/2500000000 : ℝ)
  rw [alternate_total_snoc,half_22_01_total6]
  norm_num

private theorem half_22_01_bounds7 : ∀ l,0≤half_22_01_φ7 l ∧ half_22_01_φ7 l≤1 ∧
    0≤shiftExponents 18 half_22_01_φ7 l :=
  alternate_bounds_snoc half_22_01_φ6 (49633621/1250000000 : ℝ) half_22_01_bounds6 (by norm_num)

private def half_22_01_φ8 : Fin 8 → ℝ := Fin.snoc half_22_01_φ7 (360064571/10000000000 : ℝ)

private theorem half_22_01_total8 : total half_22_01_φ8=(689300963/2000000000 : ℝ) := by
  change total (Fin.snoc half_22_01_φ7 (360064571/10000000000 : ℝ))=(689300963/2000000000 : ℝ)
  rw [alternate_total_snoc,half_22_01_total7]
  norm_num

private theorem half_22_01_bounds8 : ∀ l,0≤half_22_01_φ8 l ∧ half_22_01_φ8 l≤1 ∧
    0≤shiftExponents 18 half_22_01_φ8 l :=
  alternate_bounds_snoc half_22_01_φ7 (360064571/10000000000 : ℝ) half_22_01_bounds7 (by norm_num)

private def half_22_01_φ9 : Fin 9 → ℝ := Fin.snoc half_22_01_φ8 (128033699/5000000000 : ℝ)

private theorem half_22_01_total9 : total half_22_01_φ9=(3702572213/10000000000 : ℝ) := by
  change total (Fin.snoc half_22_01_φ8 (128033699/5000000000 : ℝ))=(3702572213/10000000000 : ℝ)
  rw [alternate_total_snoc,half_22_01_total8]
  norm_num

private theorem half_22_01_bounds9 : ∀ l,0≤half_22_01_φ9 l ∧ half_22_01_φ9 l≤1 ∧
    0≤shiftExponents 18 half_22_01_φ9 l :=
  alternate_bounds_snoc half_22_01_φ8 (128033699/5000000000 : ℝ) half_22_01_bounds8 (by norm_num)

private theorem half_22_01_prefix : PrefixCondition 18 half_22_01_φ9 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_22_01_φ1, half_22_01_φ2, half_22_01_φ3, half_22_01_φ4, half_22_01_φ5, half_22_01_φ6, half_22_01_φ7, half_22_01_φ8, half_22_01_φ9, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_22_01_hF2 : SourcePowerBound
    (paddedMoment 18 0 2 512 half_22_01_φ9) (6092283361/600000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 18) (j := 9) (r := 0) (n := 1) (D := 512)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_22_01_φ9
    (fun i => (half_22_01_bounds9 i).1) (fun i => (half_22_01_bounds9 i).2.1)
    (fun i => (half_22_01_bounds9 i).2.2) half_22_01_prefix
  convert h using 1 <;> norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, parameterExponent, curveLoss, dyadicExponent]

private theorem half_22_01_hx9 : SourcePowerBound
    (powerBoxCross 18 13 512 half_22_01_φ9) (127904857739/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 13) (r := 2) (v := 17) (w := 18) (D := 512)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_22_01_φ9 (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, parameterExponent, curveLoss, dyadicExponent]) half_22_01_hF2
    (SeedCompletionHigher18SimpleSeeds.degree18_half_17) (half_18_01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_01_hx8 : SourcePowerBound
    (powerBoxCross 18 14 256 half_22_01_φ8) (137366672617/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 8) (s := 14) (u := 12) (t := 15)
    (D := 256) (ψ := (128033699/5000000000 : ℝ)) half_22_01_φ8
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_01_bounds8 l).1) (fun l => (half_22_01_bounds8 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_13) (SeedCompletionHigher18SimpleSeeds.degree18_half_15)
    (by simpa only [half_22_01_φ9, show (2:ℝ)*256=512 by norm_num] using half_22_01_hx9)
  exact h.weaken (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_01_hx7 : SourcePowerBound
    (powerBoxCross 18 15 128 half_22_01_φ7) (150234239087/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 7) (s := 15) (u := 13) (t := 16)
    (D := 128) (ψ := (360064571/10000000000 : ℝ)) half_22_01_φ7
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_01_bounds7 l).1) (fun l => (half_22_01_bounds7 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_14) (SeedCompletionHigher18SimpleSeeds.degree18_half_16)
    (by simpa only [half_22_01_φ8, show (2:ℝ)*128=256 by norm_num] using half_22_01_hx8)
  exact h.weaken (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_01_hx6 : SourcePowerBound
    (powerBoxCross 18 16 64 half_22_01_φ6) (82700246481/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 6) (s := 16) (u := 14) (t := 17)
    (D := 64) (ψ := (49633621/1250000000 : ℝ)) half_22_01_φ6
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_01_bounds6 l).1) (fun l => (half_22_01_bounds6 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_15) (SeedCompletionHigher18SimpleSeeds.degree18_half_17)
    (by simpa only [half_22_01_φ7, show (2:ℝ)*64=128 by norm_num] using half_22_01_hx7)
  exact h.weaken (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_01_hx5 : SourcePowerBound
    (powerBoxCross 18 17 32 half_22_01_φ5) (182781791943/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 17) (u := 15) (t := 18)
    (D := 32) (ψ := (414886801/10000000000 : ℝ)) half_22_01_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_01_bounds5 l).1) (fun l => (half_22_01_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_16) (half_18_01)
    (by simpa only [half_22_01_φ6, show (2:ℝ)*32=64 by norm_num] using half_22_01_hx6)
  exact h.weaken (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_01_hx4 : SourcePowerBound
    (powerBoxCross 18 18 16 half_22_01_φ4) (202676598267/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 18) (u := 16) (t := 19)
    (D := 16) (ψ := (87705883/2000000000 : ℝ)) half_22_01_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_01_bounds4 l).1) (fun l => (half_22_01_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_17) (half_19_01)
    (by simpa only [half_22_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_22_01_hx5)
  exact h.weaken (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_01_hx3 : SourcePowerBound
    (powerBoxCross 18 19 8 half_22_01_φ3) (28046104521/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 19) (u := 17) (t := 20)
    (D := 8) (ψ := (88126663/2000000000 : ℝ)) half_22_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_01_bounds3 l).1) (fun l => (half_22_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_01) (half_20_01)
    (by simpa only [half_22_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_22_01_hx4)
  exact h.weaken (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_01_hx2 : SourcePowerBound
    (powerBoxCross 18 20 4 half_22_01_φ2) (247971470011/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 20) (u := 18) (t := 21)
    (D := 4) (ψ := (22280079/500000000 : ℝ)) half_22_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_01_bounds2 l).1) (fun l => (half_22_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_19_01) (half_21_01)
    (by simpa only [half_22_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_22_01_hx3)
  exact h.weaken (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_01_hx1 : SourcePowerBound
    (powerBoxCross 18 21 2 half_22_01_φ1) (274281110751/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 21) (u := 19) (t := 22)
    (D := 2) (ψ := (90429643/2000000000 : ℝ)) half_22_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_01_bounds1 l).1) (fun l => (half_22_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_20_01) (chord_15)
    (by simpa only [half_22_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_22_01_hx2)
  exact h.weaken (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, parameterExponent, curveLoss, dyadicExponent])

theorem half_22_01 : AdmissibleExponent 18 44 (294681560701/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 20) (ψ := (9951439/200000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_21_01)
    (by simpa only [half_22_01_φ1] using half_22_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, half_22_01_total7, half_22_01_total8, half_22_01_total9, parameterExponent, curveLoss, dyadicExponent])

theorem chord_23 : AdmissibleExponent 18 46 (1410340418183/45000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 46) (t := (8/9 : ℝ))
    (half_22_01) (half_31_00)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_23_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (25118171/500000000 : ℝ)

private theorem half_23_01_total1 : total half_23_01_φ1=(25118171/500000000 : ℝ) := by
  norm_num [half_23_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_23_01_bounds1 : ∀ l,0≤half_23_01_φ1 l ∧ half_23_01_φ1 l≤1 ∧
    0≤shiftExponents 18 half_23_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (25118171/500000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_23_01_φ2 : Fin 2 → ℝ := Fin.snoc half_23_01_φ1 (458257043/10000000000 : ℝ)

private theorem half_23_01_total2 : total half_23_01_φ2=(960620463/10000000000 : ℝ) := by
  change total (Fin.snoc half_23_01_φ1 (458257043/10000000000 : ℝ))=(960620463/10000000000 : ℝ)
  rw [alternate_total_snoc,half_23_01_total1]
  norm_num

private theorem half_23_01_bounds2 : ∀ l,0≤half_23_01_φ2 l ∧ half_23_01_φ2 l≤1 ∧
    0≤shiftExponents 18 half_23_01_φ2 l :=
  alternate_bounds_snoc half_23_01_φ1 (458257043/10000000000 : ℝ) half_23_01_bounds1 (by norm_num)

private def half_23_01_φ3 : Fin 3 → ℝ := Fin.snoc half_23_01_φ2 (56446847/1250000000 : ℝ)

private theorem half_23_01_total3 : total half_23_01_φ3=(1412195239/10000000000 : ℝ) := by
  change total (Fin.snoc half_23_01_φ2 (56446847/1250000000 : ℝ))=(1412195239/10000000000 : ℝ)
  rw [alternate_total_snoc,half_23_01_total2]
  norm_num

private theorem half_23_01_bounds3 : ∀ l,0≤half_23_01_φ3 l ∧ half_23_01_φ3 l≤1 ∧
    0≤shiftExponents 18 half_23_01_φ3 l :=
  alternate_bounds_snoc half_23_01_φ2 (56446847/1250000000 : ℝ) half_23_01_bounds2 (by norm_num)

private def half_23_01_φ4 : Fin 4 → ℝ := Fin.snoc half_23_01_φ3 (444921171/10000000000 : ℝ)

private theorem half_23_01_total4 : total half_23_01_φ4=(185711641/1000000000 : ℝ) := by
  change total (Fin.snoc half_23_01_φ3 (444921171/10000000000 : ℝ))=(185711641/1000000000 : ℝ)
  rw [alternate_total_snoc,half_23_01_total3]
  norm_num

private theorem half_23_01_bounds4 : ∀ l,0≤half_23_01_φ4 l ∧ half_23_01_φ4 l≤1 ∧
    0≤shiftExponents 18 half_23_01_φ4 l :=
  alternate_bounds_snoc half_23_01_φ3 (444921171/10000000000 : ℝ) half_23_01_bounds3 (by norm_num)

private def half_23_01_φ5 : Fin 5 → ℝ := Fin.snoc half_23_01_φ4 (439654991/10000000000 : ℝ)

private theorem half_23_01_total5 : total half_23_01_φ5=(2296771401/10000000000 : ℝ) := by
  change total (Fin.snoc half_23_01_φ4 (439654991/10000000000 : ℝ))=(2296771401/10000000000 : ℝ)
  rw [alternate_total_snoc,half_23_01_total4]
  norm_num

private theorem half_23_01_bounds5 : ∀ l,0≤half_23_01_φ5 l ∧ half_23_01_φ5 l≤1 ∧
    0≤shiftExponents 18 half_23_01_φ5 l :=
  alternate_bounds_snoc half_23_01_φ4 (439654991/10000000000 : ℝ) half_23_01_bounds4 (by norm_num)

private def half_23_01_φ6 : Fin 6 → ℝ := Fin.snoc half_23_01_φ5 (27301617/625000000 : ℝ)

private theorem half_23_01_total6 : total half_23_01_φ6=(2733597273/10000000000 : ℝ) := by
  change total (Fin.snoc half_23_01_φ5 (27301617/625000000 : ℝ))=(2733597273/10000000000 : ℝ)
  rw [alternate_total_snoc,half_23_01_total5]
  norm_num

private theorem half_23_01_bounds6 : ∀ l,0≤half_23_01_φ6 l ∧ half_23_01_φ6 l≤1 ∧
    0≤shiftExponents 18 half_23_01_φ6 l :=
  alternate_bounds_snoc half_23_01_φ5 (27301617/625000000 : ℝ) half_23_01_bounds5 (by norm_num)

private def half_23_01_φ7 : Fin 7 → ℝ := Fin.snoc half_23_01_φ6 (103277961/2500000000 : ℝ)

private theorem half_23_01_total7 : total half_23_01_φ7=(3146709117/10000000000 : ℝ) := by
  change total (Fin.snoc half_23_01_φ6 (103277961/2500000000 : ℝ))=(3146709117/10000000000 : ℝ)
  rw [alternate_total_snoc,half_23_01_total6]
  norm_num

private theorem half_23_01_bounds7 : ∀ l,0≤half_23_01_φ7 l ∧ half_23_01_φ7 l≤1 ∧
    0≤shiftExponents 18 half_23_01_φ7 l :=
  alternate_bounds_snoc half_23_01_φ6 (103277961/2500000000 : ℝ) half_23_01_bounds6 (by norm_num)

private def half_23_01_φ8 : Fin 8 → ℝ := Fin.snoc half_23_01_φ7 (196456699/5000000000 : ℝ)

private theorem half_23_01_total8 : total half_23_01_φ8=(707924503/2000000000 : ℝ) := by
  change total (Fin.snoc half_23_01_φ7 (196456699/5000000000 : ℝ))=(707924503/2000000000 : ℝ)
  rw [alternate_total_snoc,half_23_01_total7]
  norm_num

private theorem half_23_01_bounds8 : ∀ l,0≤half_23_01_φ8 l ∧ half_23_01_φ8 l≤1 ∧
    0≤shiftExponents 18 half_23_01_φ8 l :=
  alternate_bounds_snoc half_23_01_φ7 (196456699/5000000000 : ℝ) half_23_01_bounds7 (by norm_num)

private def half_23_01_φ9 : Fin 9 → ℝ := Fin.snoc half_23_01_φ8 (43517539/1250000000 : ℝ)

private theorem half_23_01_total9 : total half_23_01_φ9=(3887762827/10000000000 : ℝ) := by
  change total (Fin.snoc half_23_01_φ8 (43517539/1250000000 : ℝ))=(3887762827/10000000000 : ℝ)
  rw [alternate_total_snoc,half_23_01_total8]
  norm_num

private theorem half_23_01_bounds9 : ∀ l,0≤half_23_01_φ9 l ∧ half_23_01_φ9 l≤1 ∧
    0≤shiftExponents 18 half_23_01_φ9 l :=
  alternate_bounds_snoc half_23_01_φ8 (43517539/1250000000 : ℝ) half_23_01_bounds8 (by norm_num)

private theorem half_23_01_prefix : PrefixCondition 18 half_23_01_φ9 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_23_01_φ1, half_23_01_φ2, half_23_01_φ3, half_23_01_φ4, half_23_01_φ5, half_23_01_φ6, half_23_01_φ7, half_23_01_φ8, half_23_01_φ9, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_23_01_hF4 : SourcePowerBound
    (paddedMoment 18 0 4 512 half_23_01_φ9) (326865979621/15000000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 18) (j := 9) (r := 0) (n := 2) (D := 512)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_23_01_φ9
    (fun i => (half_23_01_bounds9 i).1) (fun i => (half_23_01_bounds9 i).2.1)
    (fun i => (half_23_01_bounds9 i).2.2) half_23_01_prefix
  convert h using 1 <;> norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, parameterExponent, curveLoss, dyadicExponent]

private theorem half_23_01_hF2 : SourcePowerBound
    (paddedMoment 18 0 2 512 half_23_01_φ9) (5536711519/600000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 18) (j := 9) (r := 0) (n := 1) (D := 512)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_23_01_φ9
    (fun i => (half_23_01_bounds9 i).1) (fun i => (half_23_01_bounds9 i).2.1)
    (fun i => (half_23_01_bounds9 i).2.2) half_23_01_prefix
  convert h using 1 <;> norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, parameterExponent, curveLoss, dyadicExponent]

private theorem half_23_01_hx9 : SourcePowerBound
    (powerBoxCross 18 14 512 half_23_01_φ9) (5291177507/400000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 14) (r := 2) (v := 4) (t := 18) (D := 512)
    (a := (7/36 : ℝ)) (b := (1/36 : ℝ)) (c := (7/9 : ℝ))
    (by norm_num) half_23_01_φ9 (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, parameterExponent, curveLoss, dyadicExponent]) half_23_01_hF2 half_23_01_hF4
    (half_18_01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, parameterExponent, curveLoss, dyadicExponent])

private theorem half_23_01_hx8 : SourcePowerBound
    (powerBoxCross 18 15 256 half_23_01_φ8) (36056285343/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 8) (s := 15) (u := 13) (t := 16)
    (D := 256) (ψ := (43517539/1250000000 : ℝ)) half_23_01_φ8
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_23_01_bounds8 l).1) (fun l => (half_23_01_bounds8 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_14) (SeedCompletionHigher18SimpleSeeds.degree18_half_16)
    (by simpa only [half_23_01_φ9, show (2:ℝ)*256=512 by norm_num] using half_23_01_hx9)
  exact h.weaken (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, parameterExponent, curveLoss, dyadicExponent])

private theorem half_23_01_hx7 : SourcePowerBound
    (powerBoxCross 18 16 128 half_23_01_φ7) (19825904717/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 7) (s := 16) (u := 14) (t := 17)
    (D := 128) (ψ := (196456699/5000000000 : ℝ)) half_23_01_φ7
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_23_01_bounds7 l).1) (fun l => (half_23_01_bounds7 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_15) (SeedCompletionHigher18SimpleSeeds.degree18_half_17)
    (by simpa only [half_23_01_φ8, show (2:ℝ)*128=256 by norm_num] using half_23_01_hx8)
  exact h.weaken (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, parameterExponent, curveLoss, dyadicExponent])

private theorem half_23_01_hx6 : SourcePowerBound
    (powerBoxCross 18 17 64 half_23_01_φ6) (175226475619/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 6) (s := 17) (u := 15) (t := 18)
    (D := 64) (ψ := (103277961/2500000000 : ℝ)) half_23_01_φ6
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_23_01_bounds6 l).1) (fun l => (half_23_01_bounds6 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_16) (half_18_01)
    (by simpa only [half_23_01_φ7, show (2:ℝ)*64=128 by norm_num] using half_23_01_hx7)
  exact h.weaken (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, parameterExponent, curveLoss, dyadicExponent])

private theorem half_23_01_hx5 : SourcePowerBound
    (powerBoxCross 18 18 32 half_23_01_φ5) (97164436009/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 18) (u := 16) (t := 19)
    (D := 32) (ψ := (27301617/625000000 : ℝ)) half_23_01_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_23_01_bounds5 l).1) (fun l => (half_23_01_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_17) (half_19_01)
    (by simpa only [half_23_01_φ6, show (2:ℝ)*32=64 by norm_num] using half_23_01_hx6)
  exact h.weaken (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, parameterExponent, curveLoss, dyadicExponent])

private theorem half_23_01_hx4 : SourcePowerBound
    (powerBoxCross 18 19 16 half_23_01_φ4) (215232153923/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 19) (u := 17) (t := 20)
    (D := 16) (ψ := (439654991/10000000000 : ℝ)) half_23_01_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_23_01_bounds4 l).1) (fun l => (half_23_01_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_01) (half_20_01)
    (by simpa only [half_23_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_23_01_hx5)
  exact h.weaken (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, parameterExponent, curveLoss, dyadicExponent])

private theorem half_23_01_hx3 : SourcePowerBound
    (powerBoxCross 18 20 8 half_23_01_φ3) (29755055399/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 20) (u := 18) (t := 21)
    (D := 8) (ψ := (444921171/10000000000 : ℝ)) half_23_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_23_01_bounds3 l).1) (fun l => (half_23_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_19_01) (half_21_01)
    (by simpa only [half_23_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_23_01_hx4)
  exact h.weaken (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, parameterExponent, curveLoss, dyadicExponent])

private theorem half_23_01_hx2 : SourcePowerBound
    (powerBoxCross 18 21 4 half_23_01_φ2) (3285594741/125000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 21) (u := 19) (t := 22)
    (D := 4) (ψ := (56446847/1250000000 : ℝ)) half_23_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_23_01_bounds2 l).1) (fun l => (half_23_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_20_01) (half_22_01)
    (by simpa only [half_23_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_23_01_hx3)
  exact h.weaken (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, parameterExponent, curveLoss, dyadicExponent])

private theorem half_23_01_hx1 : SourcePowerBound
    (powerBoxCross 18 22 2 half_23_01_φ1) (290380200463/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 22) (u := 20) (t := 23)
    (D := 2) (ψ := (458257043/10000000000 : ℝ)) half_23_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_23_01_bounds1 l).1) (fun l => (half_23_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_21_01) (chord_23)
    (by simpa only [half_23_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_23_01_hx2)
  exact h.weaken (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, parameterExponent, curveLoss, dyadicExponent])

theorem half_23_01 : AdmissibleExponent 18 46 (311981827523/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 21) (ψ := (25118171/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_22_01)
    (by simpa only [half_23_01_φ1] using half_23_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_23_01_total1, half_23_01_total2, half_23_01_total3, half_23_01_total4, half_23_01_total5, half_23_01_total6, half_23_01_total7, half_23_01_total8, half_23_01_total9, parameterExponent, curveLoss, dyadicExponent])

theorem chord_31 : AdmissibleExponent 18 48 (2647101143419/80000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 48) (t := (7/8 : ℝ))
    (half_23_01) (half_31_00)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_24_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (507511023/10000000000 : ℝ)

private theorem half_24_01_total1 : total half_24_01_φ1=(507511023/10000000000 : ℝ) := by
  norm_num [half_24_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_24_01_bounds1 : ∀ l,0≤half_24_01_φ1 l ∧ half_24_01_φ1 l≤1 ∧
    0≤shiftExponents 18 half_24_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (507511023/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_24_01_φ2 : Fin 2 → ℝ := Fin.snoc half_24_01_φ1 (464244707/10000000000 : ℝ)

private theorem half_24_01_total2 : total half_24_01_φ2=(97175573/1000000000 : ℝ) := by
  change total (Fin.snoc half_24_01_φ1 (464244707/10000000000 : ℝ))=(97175573/1000000000 : ℝ)
  rw [alternate_total_snoc,half_24_01_total1]
  norm_num

private theorem half_24_01_bounds2 : ∀ l,0≤half_24_01_φ2 l ∧ half_24_01_φ2 l≤1 ∧
    0≤shiftExponents 18 half_24_01_φ2 l :=
  alternate_bounds_snoc half_24_01_φ1 (464244707/10000000000 : ℝ) half_24_01_bounds1 (by norm_num)

private def half_24_01_φ3 : Fin 3 → ℝ := Fin.snoc half_24_01_φ2 (114445947/2500000000 : ℝ)

private theorem half_24_01_total3 : total half_24_01_φ3=(714769759/5000000000 : ℝ) := by
  change total (Fin.snoc half_24_01_φ2 (114445947/2500000000 : ℝ))=(714769759/5000000000 : ℝ)
  rw [alternate_total_snoc,half_24_01_total2]
  norm_num

private theorem half_24_01_bounds3 : ∀ l,0≤half_24_01_φ3 l ∧ half_24_01_φ3 l≤1 ∧
    0≤shiftExponents 18 half_24_01_φ3 l :=
  alternate_bounds_snoc half_24_01_φ2 (114445947/2500000000 : ℝ) half_24_01_bounds2 (by norm_num)

private def half_24_01_φ4 : Fin 4 → ℝ := Fin.snoc half_24_01_φ3 (112782173/2500000000 : ℝ)

private theorem half_24_01_total4 : total half_24_01_φ4=(188066821/1000000000 : ℝ) := by
  change total (Fin.snoc half_24_01_φ3 (112782173/2500000000 : ℝ))=(188066821/1000000000 : ℝ)
  rw [alternate_total_snoc,half_24_01_total3]
  norm_num

private theorem half_24_01_bounds4 : ∀ l,0≤half_24_01_φ4 l ∧ half_24_01_φ4 l≤1 ∧
    0≤shiftExponents 18 half_24_01_φ4 l :=
  alternate_bounds_snoc half_24_01_φ3 (112782173/2500000000 : ℝ) half_24_01_bounds3 (by norm_num)

private def half_24_01_φ5 : Fin 5 → ℝ := Fin.snoc half_24_01_φ4 (222294543/5000000000 : ℝ)

private theorem half_24_01_total5 : total half_24_01_φ5=(145328581/625000000 : ℝ) := by
  change total (Fin.snoc half_24_01_φ4 (222294543/5000000000 : ℝ))=(145328581/625000000 : ℝ)
  rw [alternate_total_snoc,half_24_01_total4]
  norm_num

private theorem half_24_01_bounds5 : ∀ l,0≤half_24_01_φ5 l ∧ half_24_01_φ5 l≤1 ∧
    0≤shiftExponents 18 half_24_01_φ5 l :=
  alternate_bounds_snoc half_24_01_φ4 (222294543/5000000000 : ℝ) half_24_01_bounds4 (by norm_num)

private def half_24_01_φ6 : Fin 6 → ℝ := Fin.snoc half_24_01_φ5 (219818521/5000000000 : ℝ)

private theorem half_24_01_total6 : total half_24_01_φ6=(1382447169/5000000000 : ℝ) := by
  change total (Fin.snoc half_24_01_φ5 (219818521/5000000000 : ℝ))=(1382447169/5000000000 : ℝ)
  rw [alternate_total_snoc,half_24_01_total5]
  norm_num

private theorem half_24_01_bounds6 : ∀ l,0≤half_24_01_φ6 l ∧ half_24_01_φ6 l≤1 ∧
    0≤shiftExponents 18 half_24_01_φ6 l :=
  alternate_bounds_snoc half_24_01_φ5 (219818521/5000000000 : ℝ) half_24_01_bounds5 (by norm_num)

private def half_24_01_φ7 : Fin 7 → ℝ := Fin.snoc half_24_01_φ6 (8511889/200000000 : ℝ)

private theorem half_24_01_total7 : total half_24_01_φ7=(797622197/2500000000 : ℝ) := by
  change total (Fin.snoc half_24_01_φ6 (8511889/200000000 : ℝ))=(797622197/2500000000 : ℝ)
  rw [alternate_total_snoc,half_24_01_total6]
  norm_num

private theorem half_24_01_bounds7 : ∀ l,0≤half_24_01_φ7 l ∧ half_24_01_φ7 l≤1 ∧
    0≤shiftExponents 18 half_24_01_φ7 l :=
  alternate_bounds_snoc half_24_01_φ6 (8511889/200000000 : ℝ) half_24_01_bounds6 (by norm_num)

private def half_24_01_φ8 : Fin 8 → ℝ := Fin.snoc half_24_01_φ7 (200279741/5000000000 : ℝ)

private theorem half_24_01_total8 : total half_24_01_φ8=(359104827/1000000000 : ℝ) := by
  change total (Fin.snoc half_24_01_φ7 (200279741/5000000000 : ℝ))=(359104827/1000000000 : ℝ)
  rw [alternate_total_snoc,half_24_01_total7]
  norm_num

private theorem half_24_01_bounds8 : ∀ l,0≤half_24_01_φ8 l ∧ half_24_01_φ8 l≤1 ∧
    0≤shiftExponents 18 half_24_01_φ8 l :=
  alternate_bounds_snoc half_24_01_φ7 (200279741/5000000000 : ℝ) half_24_01_bounds7 (by norm_num)

private def half_24_01_φ9 : Fin 9 → ℝ := Fin.snoc half_24_01_φ8 (93377951/2500000000 : ℝ)

private theorem half_24_01_total9 : total half_24_01_φ9=(1982280037/5000000000 : ℝ) := by
  change total (Fin.snoc half_24_01_φ8 (93377951/2500000000 : ℝ))=(1982280037/5000000000 : ℝ)
  rw [alternate_total_snoc,half_24_01_total8]
  norm_num

private theorem half_24_01_bounds9 : ∀ l,0≤half_24_01_φ9 l ∧ half_24_01_φ9 l≤1 ∧
    0≤shiftExponents 18 half_24_01_φ9 l :=
  alternate_bounds_snoc half_24_01_φ8 (93377951/2500000000 : ℝ) half_24_01_bounds8 (by norm_num)

private def half_24_01_φ10 : Fin 10 → ℝ := Fin.snoc half_24_01_φ9 (28754087/1000000000 : ℝ)

private theorem half_24_01_total10 : total half_24_01_φ10=(265756309/625000000 : ℝ) := by
  change total (Fin.snoc half_24_01_φ9 (28754087/1000000000 : ℝ))=(265756309/625000000 : ℝ)
  rw [alternate_total_snoc,half_24_01_total9]
  norm_num

private theorem half_24_01_bounds10 : ∀ l,0≤half_24_01_φ10 l ∧ half_24_01_φ10 l≤1 ∧
    0≤shiftExponents 18 half_24_01_φ10 l :=
  alternate_bounds_snoc half_24_01_φ9 (28754087/1000000000 : ℝ) half_24_01_bounds9 (by norm_num)

private theorem half_24_01_prefix : PrefixCondition 18 half_24_01_φ10 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_24_01_φ1, half_24_01_φ2, half_24_01_φ3, half_24_01_φ4, half_24_01_φ5, half_24_01_φ6, half_24_01_φ7, half_24_01_φ8, half_24_01_φ9, half_24_01_φ10, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_24_01_hF2 : SourcePowerBound
    (paddedMoment 18 0 2 1024 half_24_01_φ10) (390231073/37500000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 18) (j := 10) (r := 0) (n := 1) (D := 1024)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_24_01_φ10
    (fun i => (half_24_01_bounds10 i).1) (fun i => (half_24_01_bounds10 i).2.1)
    (fun i => (half_24_01_bounds10 i).2.2) half_24_01_prefix
  convert h using 1 <;> norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, parameterExponent, curveLoss, dyadicExponent]

private theorem half_24_01_hx10 : SourcePowerBound
    (powerBoxCross 18 14 1024 half_24_01_φ10) (12890863397/1000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 14) (r := 2) (v := 18) (w := 19) (D := 1024)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_24_01_φ10 (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, parameterExponent, curveLoss, dyadicExponent]) half_24_01_hF2
    (half_18_01) (half_19_01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, parameterExponent, curveLoss, dyadicExponent])

private theorem half_24_01_hx9 : SourcePowerBound
    (powerBoxCross 18 15 512 half_24_01_φ9) (138934724769/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 9) (s := 15) (u := 13) (t := 16)
    (D := 512) (ψ := (28754087/1000000000 : ℝ)) half_24_01_φ9
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_24_01_bounds9 l).1) (fun l => (half_24_01_bounds9 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_14) (SeedCompletionHigher18SimpleSeeds.degree18_half_16)
    (by simpa only [half_24_01_φ10, show (2:ℝ)*512=1024 by norm_num] using half_24_01_hx10)
  exact h.weaken (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, parameterExponent, curveLoss, dyadicExponent])

private theorem half_24_01_hx8 : SourcePowerBound
    (powerBoxCross 18 16 256 half_24_01_φ8) (152200340167/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 8) (s := 16) (u := 14) (t := 17)
    (D := 256) (ψ := (93377951/2500000000 : ℝ)) half_24_01_φ8
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_24_01_bounds8 l).1) (fun l => (half_24_01_bounds8 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_15) (SeedCompletionHigher18SimpleSeeds.degree18_half_17)
    (by simpa only [half_24_01_φ9, show (2:ℝ)*256=512 by norm_num] using half_24_01_hx9)
  exact h.weaken (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, parameterExponent, curveLoss, dyadicExponent])

private theorem half_24_01_hx7 : SourcePowerBound
    (powerBoxCross 18 17 128 half_24_01_φ7) (41935366719/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 7) (s := 17) (u := 15) (t := 18)
    (D := 128) (ψ := (200279741/5000000000 : ℝ)) half_24_01_φ7
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_24_01_bounds7 l).1) (fun l => (half_24_01_bounds7 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_16) (half_18_01)
    (by simpa only [half_24_01_φ8, show (2:ℝ)*128=256 by norm_num] using half_24_01_hx8)
  exact h.weaken (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, parameterExponent, curveLoss, dyadicExponent])

private theorem half_24_01_hx6 : SourcePowerBound
    (powerBoxCross 18 18 64 half_24_01_φ6) (92853897239/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 6) (s := 18) (u := 16) (t := 19)
    (D := 64) (ψ := (8511889/200000000 : ℝ)) half_24_01_φ6
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_24_01_bounds6 l).1) (fun l => (half_24_01_bounds6 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_17) (half_19_01)
    (by simpa only [half_24_01_φ7, show (2:ℝ)*64=128 by norm_num] using half_24_01_hx7)
  exact h.weaken (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, parameterExponent, curveLoss, dyadicExponent])

private theorem half_24_01_hx5 : SourcePowerBound
    (powerBoxCross 18 19 32 half_24_01_φ5) (102919461833/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 19) (u := 17) (t := 20)
    (D := 32) (ψ := (219818521/5000000000 : ℝ)) half_24_01_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_24_01_bounds5 l).1) (fun l => (half_24_01_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_01) (half_20_01)
    (by simpa only [half_24_01_φ6, show (2:ℝ)*32=64 by norm_num] using half_24_01_hx6)
  exact h.weaken (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, parameterExponent, curveLoss, dyadicExponent])

private theorem half_24_01_hx4 : SourcePowerBound
    (powerBoxCross 18 20 16 half_24_01_φ4) (45570670929/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 20) (u := 18) (t := 21)
    (D := 16) (ψ := (222294543/5000000000 : ℝ)) half_24_01_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_24_01_bounds4 l).1) (fun l => (half_24_01_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_19_01) (half_21_01)
    (by simpa only [half_24_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_24_01_hx5)
  exact h.weaken (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, parameterExponent, curveLoss, dyadicExponent])

private theorem half_24_01_hx3 : SourcePowerBound
    (powerBoxCross 18 21 8 half_24_01_φ3) (62962608613/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 21) (u := 19) (t := 22)
    (D := 8) (ψ := (112782173/2500000000 : ℝ)) half_24_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_24_01_bounds3 l).1) (fun l => (half_24_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_20_01) (half_22_01)
    (by simpa only [half_24_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_24_01_hx4)
  exact h.weaken (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, parameterExponent, curveLoss, dyadicExponent])

private theorem half_24_01_hx2 : SourcePowerBound
    (powerBoxCross 18 22 4 half_24_01_φ2) (277882268509/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 22) (u := 20) (t := 23)
    (D := 4) (ψ := (114445947/2500000000 : ℝ)) half_24_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_24_01_bounds2 l).1) (fun l => (half_24_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_21_01) (half_23_01)
    (by simpa only [half_24_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_24_01_hx3)
  exact h.weaken (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, parameterExponent, curveLoss, dyadicExponent])

private theorem half_24_01_hx1 : SourcePowerBound
    (powerBoxCross 18 23 2 half_24_01_φ1) (76663979229/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 23) (u := 21) (t := 24)
    (D := 2) (ψ := (464244707/10000000000 : ℝ)) half_24_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_24_01_bounds1 l).1) (fun l => (half_24_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_22_01) (chord_31)
    (by simpa only [half_24_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_24_01_hx2)
  exact h.weaken (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, parameterExponent, curveLoss, dyadicExponent])

theorem half_24_01 : AdmissibleExponent 18 48 (329493912951/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 22) (ψ := (507511023/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_23_01)
    (by simpa only [half_24_01_φ1] using half_24_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_24_01_total1, half_24_01_total2, half_24_01_total3, half_24_01_total4, half_24_01_total5, half_24_01_total6, half_24_01_total7, half_24_01_total8, half_24_01_total9, half_24_01_total10, parameterExponent, curveLoss, dyadicExponent])

theorem chord_38 : AdmissibleExponent 18 50 (152511989279/4375000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 50) (t := (6/7 : ℝ))
    (half_24_01) (half_31_00)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_25_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (513156803/10000000000 : ℝ)

private theorem half_25_01_total1 : total half_25_01_φ1=(513156803/10000000000 : ℝ) := by
  norm_num [half_25_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_25_01_bounds1 : ∀ l,0≤half_25_01_φ1 l ∧ half_25_01_φ1 l≤1 ∧
    0≤shiftExponents 18 half_25_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (513156803/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_25_01_φ2 : Fin 2 → ℝ := Fin.snoc half_25_01_φ1 (470384677/10000000000 : ℝ)

private theorem half_25_01_total2 : total half_25_01_φ2=(24588537/250000000 : ℝ) := by
  change total (Fin.snoc half_25_01_φ1 (470384677/10000000000 : ℝ))=(24588537/250000000 : ℝ)
  rw [alternate_total_snoc,half_25_01_total1]
  norm_num

private theorem half_25_01_bounds2 : ∀ l,0≤half_25_01_φ2 l ∧ half_25_01_φ2 l≤1 ∧
    0≤shiftExponents 18 half_25_01_φ2 l :=
  alternate_bounds_snoc half_25_01_φ1 (470384677/10000000000 : ℝ) half_25_01_bounds1 (by norm_num)

private def half_25_01_φ3 : Fin 3 → ℝ := Fin.snoc half_25_01_φ2 (464006017/10000000000 : ℝ)

private theorem half_25_01_total3 : total half_25_01_φ3=(1447547497/10000000000 : ℝ) := by
  change total (Fin.snoc half_25_01_φ2 (464006017/10000000000 : ℝ))=(1447547497/10000000000 : ℝ)
  rw [alternate_total_snoc,half_25_01_total2]
  norm_num

private theorem half_25_01_bounds3 : ∀ l,0≤half_25_01_φ3 l ∧ half_25_01_φ3 l≤1 ∧
    0≤shiftExponents 18 half_25_01_φ3 l :=
  alternate_bounds_snoc half_25_01_φ2 (464006017/10000000000 : ℝ) half_25_01_bounds2 (by norm_num)

private def half_25_01_φ4 : Fin 4 → ℝ := Fin.snoc half_25_01_φ3 (457897519/10000000000 : ℝ)

private theorem half_25_01_total4 : total half_25_01_φ4=(238180627/1250000000 : ℝ) := by
  change total (Fin.snoc half_25_01_φ3 (457897519/10000000000 : ℝ))=(238180627/1250000000 : ℝ)
  rw [alternate_total_snoc,half_25_01_total3]
  norm_num

private theorem half_25_01_bounds4 : ∀ l,0≤half_25_01_φ4 l ∧ half_25_01_φ4 l≤1 ∧
    0≤shiftExponents 18 half_25_01_φ4 l :=
  alternate_bounds_snoc half_25_01_φ3 (457897519/10000000000 : ℝ) half_25_01_bounds3 (by norm_num)

private def half_25_01_φ5 : Fin 5 → ℝ := Fin.snoc half_25_01_φ4 (14131613/312500000 : ℝ)

private theorem half_25_01_total5 : total half_25_01_φ5=(294707079/1250000000 : ℝ) := by
  change total (Fin.snoc half_25_01_φ4 (14131613/312500000 : ℝ))=(294707079/1250000000 : ℝ)
  rw [alternate_total_snoc,half_25_01_total4]
  norm_num

private theorem half_25_01_bounds5 : ∀ l,0≤half_25_01_φ5 l ∧ half_25_01_φ5 l≤1 ∧
    0≤shiftExponents 18 half_25_01_φ5 l :=
  alternate_bounds_snoc half_25_01_φ4 (14131613/312500000 : ℝ) half_25_01_bounds4 (by norm_num)

private def half_25_01_φ6 : Fin 6 → ℝ := Fin.snoc half_25_01_φ5 (89664757/2000000000 : ℝ)

private theorem half_25_01_total6 : total half_25_01_φ6=(2805980417/10000000000 : ℝ) := by
  change total (Fin.snoc half_25_01_φ5 (89664757/2000000000 : ℝ))=(2805980417/10000000000 : ℝ)
  rw [alternate_total_snoc,half_25_01_total5]
  norm_num

private theorem half_25_01_bounds6 : ∀ l,0≤half_25_01_φ6 l ∧ half_25_01_φ6 l≤1 ∧
    0≤shiftExponents 18 half_25_01_φ6 l :=
  alternate_bounds_snoc half_25_01_φ5 (89664757/2000000000 : ℝ) half_25_01_bounds5 (by norm_num)

private def half_25_01_φ7 : Fin 7 → ℝ := Fin.snoc half_25_01_φ6 (211588811/5000000000 : ℝ)

private theorem half_25_01_total7 : total half_25_01_φ7=(3229158039/10000000000 : ℝ) := by
  change total (Fin.snoc half_25_01_φ6 (211588811/5000000000 : ℝ))=(3229158039/10000000000 : ℝ)
  rw [alternate_total_snoc,half_25_01_total6]
  norm_num

private theorem half_25_01_bounds7 : ∀ l,0≤half_25_01_φ7 l ∧ half_25_01_φ7 l≤1 ∧
    0≤shiftExponents 18 half_25_01_φ7 l :=
  alternate_bounds_snoc half_25_01_φ6 (211588811/5000000000 : ℝ) half_25_01_bounds6 (by norm_num)

private def half_25_01_φ8 : Fin 8 → ℝ := Fin.snoc half_25_01_φ7 (19914241/500000000 : ℝ)

private theorem half_25_01_total8 : total half_25_01_φ8=(3627442859/10000000000 : ℝ) := by
  change total (Fin.snoc half_25_01_φ7 (19914241/500000000 : ℝ))=(3627442859/10000000000 : ℝ)
  rw [alternate_total_snoc,half_25_01_total7]
  norm_num

private theorem half_25_01_bounds8 : ∀ l,0≤half_25_01_φ8 l ∧ half_25_01_φ8 l≤1 ∧
    0≤shiftExponents 18 half_25_01_φ8 l :=
  alternate_bounds_snoc half_25_01_φ7 (19914241/500000000 : ℝ) half_25_01_bounds7 (by norm_num)

private def half_25_01_φ9 : Fin 9 → ℝ := Fin.snoc half_25_01_φ8 (187428151/5000000000 : ℝ)

private theorem half_25_01_total9 : total half_25_01_φ9=(4002299161/10000000000 : ℝ) := by
  change total (Fin.snoc half_25_01_φ8 (187428151/5000000000 : ℝ))=(4002299161/10000000000 : ℝ)
  rw [alternate_total_snoc,half_25_01_total8]
  norm_num

private theorem half_25_01_bounds9 : ∀ l,0≤half_25_01_φ9 l ∧ half_25_01_φ9 l≤1 ∧
    0≤shiftExponents 18 half_25_01_φ9 l :=
  alternate_bounds_snoc half_25_01_φ8 (187428151/5000000000 : ℝ) half_25_01_bounds8 (by norm_num)

private def half_25_01_φ10 : Fin 10 → ℝ := Fin.snoc half_25_01_φ9 (352805931/10000000000 : ℝ)

private theorem half_25_01_total10 : total half_25_01_φ10=(1088776273/2500000000 : ℝ) := by
  change total (Fin.snoc half_25_01_φ9 (352805931/10000000000 : ℝ))=(1088776273/2500000000 : ℝ)
  rw [alternate_total_snoc,half_25_01_total9]
  norm_num

private theorem half_25_01_bounds10 : ∀ l,0≤half_25_01_φ10 l ∧ half_25_01_φ10 l≤1 ∧
    0≤shiftExponents 18 half_25_01_φ10 l :=
  alternate_bounds_snoc half_25_01_φ9 (352805931/10000000000 : ℝ) half_25_01_bounds9 (by norm_num)

private theorem half_25_01_prefix : PrefixCondition 18 half_25_01_φ10 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_25_01_φ1, half_25_01_φ2, half_25_01_φ3, half_25_01_φ4, half_25_01_φ5, half_25_01_φ6, half_25_01_φ7, half_25_01_φ8, half_25_01_φ9, half_25_01_φ10, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_25_01_hF4 : SourcePowerBound
    (paddedMoment 18 0 4 1024 half_25_01_φ10) (87286599679/3750000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 18) (j := 10) (r := 0) (n := 2) (D := 1024)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_25_01_φ10
    (fun i => (half_25_01_bounds10 i).1) (fun i => (half_25_01_bounds10 i).2.1)
    (fun i => (half_25_01_bounds10 i).2.2) half_25_01_prefix
  convert h using 1 <;> norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, parameterExponent, curveLoss, dyadicExponent]

private theorem half_25_01_hF2 : SourcePowerBound
    (paddedMoment 18 0 2 1024 half_25_01_φ10) (1483671181/150000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 18) (j := 10) (r := 0) (n := 1) (D := 1024)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_25_01_φ10
    (fun i => (half_25_01_bounds10 i).1) (fun i => (half_25_01_bounds10 i).2.1)
    (fun i => (half_25_01_bounds10 i).2.2) half_25_01_prefix
  convert h using 1 <;> norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, parameterExponent, curveLoss, dyadicExponent]

private theorem half_25_01_hx10 : SourcePowerBound
    (powerBoxCross 18 15 1024 half_25_01_φ10) (67452417289/5000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 15) (r := 2) (v := 4) (t := 19) (D := 1024)
    (a := (13/76 : ℝ)) (b := (3/76 : ℝ)) (c := (15/19 : ℝ))
    (by norm_num) half_25_01_φ10 (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, parameterExponent, curveLoss, dyadicExponent]) half_25_01_hF2 half_25_01_hF4
    (half_19_01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, parameterExponent, curveLoss, dyadicExponent])

private theorem half_25_01_hx9 : SourcePowerBound
    (powerBoxCross 18 16 512 half_25_01_φ9) (147036294663/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 9) (s := 16) (u := 14) (t := 17)
    (D := 512) (ψ := (352805931/10000000000 : ℝ)) half_25_01_φ9
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_25_01_bounds9 l).1) (fun l => (half_25_01_bounds9 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_15) (SeedCompletionHigher18SimpleSeeds.degree18_half_17)
    (by simpa only [half_25_01_φ10, show (2:ℝ)*512=1024 by norm_num] using half_25_01_hx10)
  exact h.weaken (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, parameterExponent, curveLoss, dyadicExponent])

private theorem half_25_01_hx8 : SourcePowerBound
    (powerBoxCross 18 17 256 half_25_01_φ8) (40267644301/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 8) (s := 17) (u := 15) (t := 18)
    (D := 256) (ψ := (187428151/5000000000 : ℝ)) half_25_01_φ8
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_25_01_bounds8 l).1) (fun l => (half_25_01_bounds8 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_16) (half_18_01)
    (by simpa only [half_25_01_φ9, show (2:ℝ)*256=512 by norm_num] using half_25_01_hx9)
  exact h.weaken (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, parameterExponent, curveLoss, dyadicExponent])

private theorem half_25_01_hx7 : SourcePowerBound
    (powerBoxCross 18 18 128 half_25_01_φ7) (88654198933/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 7) (s := 18) (u := 16) (t := 19)
    (D := 128) (ψ := (19914241/500000000 : ℝ)) half_25_01_φ7
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_25_01_bounds7 l).1) (fun l => (half_25_01_bounds7 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher18SimpleSeeds.degree18_half_17) (half_19_01)
    (by simpa only [half_25_01_φ8, show (2:ℝ)*128=256 by norm_num] using half_25_01_hx8)
  exact h.weaken (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, parameterExponent, curveLoss, dyadicExponent])

private theorem half_25_01_hx6 : SourcePowerBound
    (powerBoxCross 18 19 64 half_25_01_φ6) (97998911903/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 6) (s := 19) (u := 17) (t := 20)
    (D := 64) (ψ := (211588811/5000000000 : ℝ)) half_25_01_φ6
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_25_01_bounds6 l).1) (fun l => (half_25_01_bounds6 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_01) (half_20_01)
    (by simpa only [half_25_01_φ7, show (2:ℝ)*64=128 by norm_num] using half_25_01_hx7)
  exact h.weaken (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, parameterExponent, curveLoss, dyadicExponent])

private theorem half_25_01_hx5 : SourcePowerBound
    (powerBoxCross 18 20 32 half_25_01_φ5) (217326992739/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 20) (u := 18) (t := 21)
    (D := 32) (ψ := (89664757/2000000000 : ℝ)) half_25_01_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_25_01_bounds5 l).1) (fun l => (half_25_01_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_19_01) (half_21_01)
    (by simpa only [half_25_01_φ6, show (2:ℝ)*32=64 by norm_num] using half_25_01_hx6)
  exact h.weaken (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, parameterExponent, curveLoss, dyadicExponent])

private theorem half_25_01_hx4 : SourcePowerBound
    (powerBoxCross 18 21 16 half_25_01_φ4) (240551145039/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 21) (u := 19) (t := 22)
    (D := 16) (ψ := (14131613/312500000 : ℝ)) half_25_01_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_25_01_bounds4 l).1) (fun l => (half_25_01_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_20_01) (half_22_01)
    (by simpa only [half_25_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_25_01_hx5)
  exact h.weaken (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, parameterExponent, curveLoss, dyadicExponent])

private theorem half_25_01_hx3 : SourcePowerBound
    (powerBoxCross 18 22 8 half_25_01_φ3) (265768806019/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 22) (u := 20) (t := 23)
    (D := 8) (ψ := (457897519/10000000000 : ℝ)) half_25_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_25_01_bounds3 l).1) (fun l => (half_25_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_21_01) (half_23_01)
    (by simpa only [half_25_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_25_01_hx4)
  exact h.weaken (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, parameterExponent, curveLoss, dyadicExponent])

private theorem half_25_01_hx2 : SourcePowerBound
    (powerBoxCross 18 23 4 half_25_01_φ2) (293043839731/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 23) (u := 21) (t := 24)
    (D := 4) (ψ := (464006017/10000000000 : ℝ)) half_25_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_25_01_bounds2 l).1) (fun l => (half_25_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_22_01) (half_24_01)
    (by simpa only [half_25_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_25_01_hx3)
  exact h.weaken (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, parameterExponent, curveLoss, dyadicExponent])

private theorem half_25_01_hx1 : SourcePowerBound
    (powerBoxCross 18 24 2 half_25_01_φ1) (80774716367/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 24) (u := 22) (t := 25)
    (D := 2) (ψ := (470384677/10000000000 : ℝ)) half_25_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_25_01_bounds1 l).1) (fun l => (half_25_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_23_01) (chord_38)
    (by simpa only [half_25_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_25_01_hx2)
  exact h.weaken (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, parameterExponent, curveLoss, dyadicExponent])

theorem half_25_01 : AdmissibleExponent 18 50 (347217235209/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 23) (ψ := (513156803/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_24_01)
    (by simpa only [half_25_01_φ1] using half_25_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_25_01_total1, half_25_01_total2, half_25_01_total3, half_25_01_total4, half_25_01_total5, half_25_01_total6, half_25_01_total7, half_25_01_total8, half_25_01_total9, half_25_01_total10, parameterExponent, curveLoss, dyadicExponent])

theorem chord_44 : AdmissibleExponent 18 52 (2199314526803/60000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 52) (t := (5/6 : ℝ))
    (half_25_01) (half_31_00)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

#print axioms chord_44
end Waring.SeedCompletionAlternate18Seeds
