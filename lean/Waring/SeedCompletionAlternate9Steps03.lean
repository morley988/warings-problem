import Waring.SeedCompletionAlternate9Steps02

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionAlternate9Seeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges SeedCompletionDivisorPowerScales
open PolicyCompletionSharpResidualSource

private def half_21_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1111111111/10000000000 : ℝ)

private theorem half_21_02_total1 : total half_21_02_φ1=(1111111111/10000000000 : ℝ) := by
  norm_num [half_21_02_φ1,total,emptyPhi,Fin.snoc]

private theorem half_21_02_bounds1 : ∀ l,0≤half_21_02_φ1 l ∧ half_21_02_φ1 l≤1 ∧
    0≤shiftExponents 9 half_21_02_φ1 l :=
  alternate_bounds_snoc emptyPhi (1111111111/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_21_02_φ2 : Fin 2 → ℝ := Fin.snoc half_21_02_φ1 (1080199923/10000000000 : ℝ)

private theorem half_21_02_total2 : total half_21_02_φ2=(1095655517/5000000000 : ℝ) := by
  change total (Fin.snoc half_21_02_φ1 (1080199923/10000000000 : ℝ))=(1095655517/5000000000 : ℝ)
  rw [alternate_total_snoc,half_21_02_total1]
  norm_num

private theorem half_21_02_bounds2 : ∀ l,0≤half_21_02_φ2 l ∧ half_21_02_φ2 l≤1 ∧
    0≤shiftExponents 9 half_21_02_φ2 l :=
  alternate_bounds_snoc half_21_02_φ1 (1080199923/10000000000 : ℝ) half_21_02_bounds1 (by norm_num)

private def half_21_02_φ3 : Fin 3 → ℝ := Fin.snoc half_21_02_φ2 (24402153/250000000 : ℝ)

private theorem half_21_02_total3 : total half_21_02_φ3=(1583698577/5000000000 : ℝ) := by
  change total (Fin.snoc half_21_02_φ2 (24402153/250000000 : ℝ))=(1583698577/5000000000 : ℝ)
  rw [alternate_total_snoc,half_21_02_total2]
  norm_num

private theorem half_21_02_bounds3 : ∀ l,0≤half_21_02_φ3 l ∧ half_21_02_φ3 l≤1 ∧
    0≤shiftExponents 9 half_21_02_φ3 l :=
  alternate_bounds_snoc half_21_02_φ2 (24402153/250000000 : ℝ) half_21_02_bounds2 (by norm_num)

private def half_21_02_φ4 : Fin 4 → ℝ := Fin.snoc half_21_02_φ3 (170815071/2000000000 : ℝ)

private theorem half_21_02_total4 : total half_21_02_φ4=(4021472509/10000000000 : ℝ) := by
  change total (Fin.snoc half_21_02_φ3 (170815071/2000000000 : ℝ))=(4021472509/10000000000 : ℝ)
  rw [alternate_total_snoc,half_21_02_total3]
  norm_num

private theorem half_21_02_bounds4 : ∀ l,0≤half_21_02_φ4 l ∧ half_21_02_φ4 l≤1 ∧
    0≤shiftExponents 9 half_21_02_φ4 l :=
  alternate_bounds_snoc half_21_02_φ3 (170815071/2000000000 : ℝ) half_21_02_bounds3 (by norm_num)

private def half_21_02_φ5 : Fin 5 → ℝ := Fin.snoc half_21_02_φ4 (23353623/312500000 : ℝ)

private theorem half_21_02_total5 : total half_21_02_φ5=(953757689/2000000000 : ℝ) := by
  change total (Fin.snoc half_21_02_φ4 (23353623/312500000 : ℝ))=(953757689/2000000000 : ℝ)
  rw [alternate_total_snoc,half_21_02_total4]
  norm_num

private theorem half_21_02_bounds5 : ∀ l,0≤half_21_02_φ5 l ∧ half_21_02_φ5 l≤1 ∧
    0≤shiftExponents 9 half_21_02_φ5 l :=
  alternate_bounds_snoc half_21_02_φ4 (23353623/312500000 : ℝ) half_21_02_bounds4 (by norm_num)

private def half_21_02_φ6 : Fin 6 → ℝ := Fin.snoc half_21_02_φ5 (163475361/2500000000 : ℝ)

private theorem half_21_02_total6 : total half_21_02_φ6=(5422689889/10000000000 : ℝ) := by
  change total (Fin.snoc half_21_02_φ5 (163475361/2500000000 : ℝ))=(5422689889/10000000000 : ℝ)
  rw [alternate_total_snoc,half_21_02_total5]
  norm_num

private theorem half_21_02_bounds6 : ∀ l,0≤half_21_02_φ6 l ∧ half_21_02_φ6 l≤1 ∧
    0≤shiftExponents 9 half_21_02_φ6 l :=
  alternate_bounds_snoc half_21_02_φ5 (163475361/2500000000 : ℝ) half_21_02_bounds5 (by norm_num)

private theorem half_21_02_prefix : PrefixCondition 9 half_21_02_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_21_02_φ1, half_21_02_φ2, half_21_02_φ3, half_21_02_φ4, half_21_02_φ5, half_21_02_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_21_02_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_21_02_φ6) (8731930333/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_21_02_φ6
    (fun i => (half_21_02_bounds6 i).1) (fun i => (half_21_02_bounds6 i).2.1)
    (fun i => (half_21_02_bounds6 i).2.2) half_21_02_prefix
  convert h using 1 <;> norm_num [half_21_02_total1, half_21_02_total2, half_21_02_total3, half_21_02_total4, half_21_02_total5, half_21_02_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_21_02_hx6 : SourcePowerBound
    (powerBoxCross 9 15 64 half_21_02_φ6) (31186443187/2500000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 15) (r := 2) (v := 0) (w := 20) (D := 64)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_21_02_φ6 (by norm_num [half_21_02_total1, half_21_02_total2, half_21_02_total3, half_21_02_total4, half_21_02_total5, half_21_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_21_02_total1, half_21_02_total2, half_21_02_total3, half_21_02_total4, half_21_02_total5, half_21_02_total6, parameterExponent, curveLoss, dyadicExponent]) half_21_02_hF2
    (admissibleExponent_zero 9) (half_20_02)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_21_02_total1, half_21_02_total2, half_21_02_total3, half_21_02_total4, half_21_02_total5, half_21_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_02_hx5 : SourcePowerBound
    (powerBoxCross 9 16 32 half_21_02_φ5) (72142338013/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 16) (u := 14) (t := 17)
    (D := 32) (ψ := (163475361/2500000000 : ℝ)) half_21_02_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_02_bounds5 l).1) (fun l => (half_21_02_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_02_total1, half_21_02_total2, half_21_02_total3, half_21_02_total4, half_21_02_total5, half_21_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_02) (half_17_02)
    (by simpa only [half_21_02_φ6, show (2:ℝ)*32=64 by norm_num] using half_21_02_hx6)
  exact h.weaken (by norm_num [half_21_02_total1, half_21_02_total2, half_21_02_total3, half_21_02_total4, half_21_02_total5, half_21_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_02_hx4 : SourcePowerBound
    (powerBoxCross 9 17 16 half_21_02_φ4) (42349261037/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 17) (u := 15) (t := 18)
    (D := 16) (ψ := (23353623/312500000 : ℝ)) half_21_02_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_02_bounds4 l).1) (fun l => (half_21_02_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_02_total1, half_21_02_total2, half_21_02_total3, half_21_02_total4, half_21_02_total5, half_21_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_02) (half_18_02)
    (by simpa only [half_21_02_φ5, show (2:ℝ)*16=32 by norm_num] using half_21_02_hx5)
  exact h.weaken (by norm_num [half_21_02_total1, half_21_02_total2, half_21_02_total3, half_21_02_total4, half_21_02_total5, half_21_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_02_hx3 : SourcePowerBound
    (powerBoxCross 9 18 8 half_21_02_φ3) (25148984523/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 18) (u := 16) (t := 19)
    (D := 8) (ψ := (170815071/2000000000 : ℝ)) half_21_02_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_02_bounds3 l).1) (fun l => (half_21_02_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_02_total1, half_21_02_total2, half_21_02_total3, half_21_02_total4, half_21_02_total5, half_21_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_02) (half_19_02)
    (by simpa only [half_21_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_21_02_hx4)
  exact h.weaken (by norm_num [half_21_02_total1, half_21_02_total2, half_21_02_total3, half_21_02_total4, half_21_02_total5, half_21_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_02_hx2 : SourcePowerBound
    (powerBoxCross 9 19 4 half_21_02_φ2) (120462169071/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 19) (u := 17) (t := 20)
    (D := 4) (ψ := (24402153/250000000 : ℝ)) half_21_02_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_02_bounds2 l).1) (fun l => (half_21_02_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_02_total1, half_21_02_total2, half_21_02_total3, half_21_02_total4, half_21_02_total5, half_21_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_02) (half_20_02)
    (by simpa only [half_21_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_21_02_hx3)
  exact h.weaken (by norm_num [half_21_02_total1, half_21_02_total2, half_21_02_total3, half_21_02_total4, half_21_02_total5, half_21_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_02_hx1 : SourcePowerBound
    (powerBoxCross 9 20 2 half_21_02_φ1) (288935236677/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 20) (u := 18) (t := 21)
    (D := 2) (ψ := (1080199923/10000000000 : ℝ)) half_21_02_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_02_bounds1 l).1) (fun l => (half_21_02_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_02_total1, half_21_02_total2, half_21_02_total3, half_21_02_total4, half_21_02_total5, half_21_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_19_02) (chord_61)
    (by simpa only [half_21_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_21_02_hx2)
  exact h.weaken (by norm_num [half_21_02_total1, half_21_02_total2, half_21_02_total3, half_21_02_total4, half_21_02_total5, half_21_02_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_21_02 : AdmissibleExponent 9 42 (166134285003/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 19) (ψ := (1111111111/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_20_02)
    (by simpa only [half_21_02_φ1] using half_21_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_21_02_total1, half_21_02_total2, half_21_02_total3, half_21_02_total4, half_21_02_total5, half_21_02_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_22_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1111111111/10000000000 : ℝ)

private theorem half_22_02_total1 : total half_22_02_φ1=(1111111111/10000000000 : ℝ) := by
  norm_num [half_22_02_φ1,total,emptyPhi,Fin.snoc]

private theorem half_22_02_bounds1 : ∀ l,0≤half_22_02_φ1 l ∧ half_22_02_φ1 l≤1 ∧
    0≤shiftExponents 9 half_22_02_φ1 l :=
  alternate_bounds_snoc emptyPhi (1111111111/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_22_02_φ2 : Fin 2 → ℝ := Fin.snoc half_22_02_φ1 (34091577/312500000 : ℝ)

private theorem half_22_02_total2 : total half_22_02_φ2=(88081663/400000000 : ℝ) := by
  change total (Fin.snoc half_22_02_φ1 (34091577/312500000 : ℝ))=(88081663/400000000 : ℝ)
  rw [alternate_total_snoc,half_22_02_total1]
  norm_num

private theorem half_22_02_bounds2 : ∀ l,0≤half_22_02_φ2 l ∧ half_22_02_φ2 l≤1 ∧
    0≤shiftExponents 9 half_22_02_φ2 l :=
  alternate_bounds_snoc half_22_02_φ1 (34091577/312500000 : ℝ) half_22_02_bounds1 (by norm_num)

private def half_22_02_φ3 : Fin 3 → ℝ := Fin.snoc half_22_02_φ2 (974744803/10000000000 : ℝ)

private theorem half_22_02_total3 : total half_22_02_φ3=(1588393189/5000000000 : ℝ) := by
  change total (Fin.snoc half_22_02_φ2 (974744803/10000000000 : ℝ))=(1588393189/5000000000 : ℝ)
  rw [alternate_total_snoc,half_22_02_total2]
  norm_num

private theorem half_22_02_bounds3 : ∀ l,0≤half_22_02_φ3 l ∧ half_22_02_φ3 l≤1 ∧
    0≤shiftExponents 9 half_22_02_φ3 l :=
  alternate_bounds_snoc half_22_02_φ2 (974744803/10000000000 : ℝ) half_22_02_bounds2 (by norm_num)

private def half_22_02_φ4 : Fin 4 → ℝ := Fin.snoc half_22_02_φ3 (426450851/5000000000 : ℝ)

private theorem half_22_02_total4 : total half_22_02_φ4=(50371101/125000000 : ℝ) := by
  change total (Fin.snoc half_22_02_φ3 (426450851/5000000000 : ℝ))=(50371101/125000000 : ℝ)
  rw [alternate_total_snoc,half_22_02_total3]
  norm_num

private theorem half_22_02_bounds4 : ∀ l,0≤half_22_02_φ4 l ∧ half_22_02_φ4 l≤1 ∧
    0≤shiftExponents 9 half_22_02_φ4 l :=
  alternate_bounds_snoc half_22_02_φ3 (426450851/5000000000 : ℝ) half_22_02_bounds3 (by norm_num)

private def half_22_02_φ5 : Fin 5 → ℝ := Fin.snoc half_22_02_φ4 (746288989/10000000000 : ℝ)

private theorem half_22_02_total5 : total half_22_02_φ5=(4775977069/10000000000 : ℝ) := by
  change total (Fin.snoc half_22_02_φ4 (746288989/10000000000 : ℝ))=(4775977069/10000000000 : ℝ)
  rw [alternate_total_snoc,half_22_02_total4]
  norm_num

private theorem half_22_02_bounds5 : ∀ l,0≤half_22_02_φ5 l ∧ half_22_02_φ5 l≤1 ∧
    0≤shiftExponents 9 half_22_02_φ5 l :=
  alternate_bounds_snoc half_22_02_φ4 (746288989/10000000000 : ℝ) half_22_02_bounds4 (by norm_num)

private def half_22_02_φ6 : Fin 6 → ℝ := Fin.snoc half_22_02_φ5 (326501433/5000000000 : ℝ)

private theorem half_22_02_total6 : total half_22_02_φ6=(1085795987/2000000000 : ℝ) := by
  change total (Fin.snoc half_22_02_φ5 (326501433/5000000000 : ℝ))=(1085795987/2000000000 : ℝ)
  rw [alternate_total_snoc,half_22_02_total5]
  norm_num

private theorem half_22_02_bounds6 : ∀ l,0≤half_22_02_φ6 l ∧ half_22_02_φ6 l≤1 ∧
    0≤shiftExponents 9 half_22_02_φ6 l :=
  alternate_bounds_snoc half_22_02_φ5 (326501433/5000000000 : ℝ) half_22_02_bounds5 (by norm_num)

private theorem half_22_02_prefix : PrefixCondition 9 half_22_02_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_22_02_φ1, half_22_02_φ2, half_22_02_φ3, half_22_02_φ4, half_22_02_φ5, half_22_02_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_22_02_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_22_02_φ6) (1742612039/250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_22_02_φ6
    (fun i => (half_22_02_bounds6 i).1) (fun i => (half_22_02_bounds6 i).2.1)
    (fun i => (half_22_02_bounds6 i).2.2) half_22_02_prefix
  convert h using 1 <;> norm_num [half_22_02_total1, half_22_02_total2, half_22_02_total3, half_22_02_total4, half_22_02_total5, half_22_02_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_22_02_hx6 : SourcePowerBound
    (powerBoxCross 9 16 64 half_22_02_φ6) (133728387929/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 16) (r := 2) (v := 21) (w := 22) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_22_02_φ6 (by norm_num [half_22_02_total1, half_22_02_total2, half_22_02_total3, half_22_02_total4, half_22_02_total5, half_22_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_22_02_total1, half_22_02_total2, half_22_02_total3, half_22_02_total4, half_22_02_total5, half_22_02_total6, parameterExponent, curveLoss, dyadicExponent]) half_22_02_hF2
    (half_21_02) (half_22_01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_22_02_total1, half_22_02_total2, half_22_02_total3, half_22_02_total4, half_22_02_total5, half_22_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_02_hx5 : SourcePowerBound
    (powerBoxCross 9 17 32 half_22_02_φ5) (154321073947/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 17) (u := 15) (t := 18)
    (D := 32) (ψ := (326501433/5000000000 : ℝ)) half_22_02_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_02_bounds5 l).1) (fun l => (half_22_02_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_02_total1, half_22_02_total2, half_22_02_total3, half_22_02_total4, half_22_02_total5, half_22_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_02) (half_18_02)
    (by simpa only [half_22_02_φ6, show (2:ℝ)*32=64 by norm_num] using half_22_02_hx6)
  exact h.weaken (by norm_num [half_22_02_total1, half_22_02_total2, half_22_02_total3, half_22_02_total4, half_22_02_total5, half_22_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_02_hx4 : SourcePowerBound
    (powerBoxCross 9 18 16 half_22_02_φ4) (180797089199/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 18) (u := 16) (t := 19)
    (D := 16) (ψ := (746288989/10000000000 : ℝ)) half_22_02_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_02_bounds4 l).1) (fun l => (half_22_02_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_02_total1, half_22_02_total2, half_22_02_total3, half_22_02_total4, half_22_02_total5, half_22_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_02) (half_19_02)
    (by simpa only [half_22_02_φ5, show (2:ℝ)*16=32 by norm_num] using half_22_02_hx5)
  exact h.weaken (by norm_num [half_22_02_total1, half_22_02_total2, half_22_02_total3, half_22_02_total4, half_22_02_total5, half_22_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_02_hx3 : SourcePowerBound
    (powerBoxCross 9 19 8 half_22_02_φ3) (334736079/15625000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 19) (u := 17) (t := 20)
    (D := 8) (ψ := (426450851/5000000000 : ℝ)) half_22_02_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_02_bounds3 l).1) (fun l => (half_22_02_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_02_total1, half_22_02_total2, half_22_02_total3, half_22_02_total4, half_22_02_total5, half_22_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_02) (half_20_02)
    (by simpa only [half_22_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_22_02_hx4)
  exact h.weaken (by norm_num [half_22_02_total1, half_22_02_total2, half_22_02_total3, half_22_02_total4, half_22_02_total5, half_22_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_02_hx2 : SourcePowerBound
    (powerBoxCross 9 20 4 half_22_02_φ2) (127945491289/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 20) (u := 18) (t := 21)
    (D := 4) (ψ := (974744803/10000000000 : ℝ)) half_22_02_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_02_bounds2 l).1) (fun l => (half_22_02_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_02_total1, half_22_02_total2, half_22_02_total3, half_22_02_total4, half_22_02_total5, half_22_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_19_02) (half_21_02)
    (by simpa only [half_22_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_22_02_hx3)
  exact h.weaken (by norm_num [half_22_02_total1, half_22_02_total2, half_22_02_total3, half_22_02_total4, half_22_02_total5, half_22_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_02_hx1 : SourcePowerBound
    (powerBoxCross 9 21 2 half_22_02_φ1) (306751367167/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 21) (u := 19) (t := 22)
    (D := 2) (ψ := (34091577/312500000 : ℝ)) half_22_02_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_02_bounds1 l).1) (fun l => (half_22_02_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_02_total1, half_22_02_total2, half_22_02_total3, half_22_02_total4, half_22_02_total5, half_22_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_20_02) (half_22_01)
    (by simpa only [half_22_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_22_02_hx2)
  exact h.weaken (by norm_num [half_22_02_total1, half_22_02_total2, half_22_02_total3, half_22_02_total4, half_22_02_total5, half_22_02_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_22_02 : AdmissibleExponent 9 44 (176153461359/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 20) (ψ := (1111111111/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_21_02)
    (by simpa only [half_22_02_φ1] using half_22_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_22_02_total1, half_22_02_total2, half_22_02_total3, half_22_02_total4, half_22_02_total5, half_22_02_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_10_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (890156643/10000000000 : ℝ)

private theorem half_10_03_total1 : total half_10_03_φ1=(890156643/10000000000 : ℝ) := by
  norm_num [half_10_03_φ1,total,emptyPhi,Fin.snoc]

private theorem half_10_03_bounds1 : ∀ l,0≤half_10_03_φ1 l ∧ half_10_03_φ1 l≤1 ∧
    0≤shiftExponents 9 half_10_03_φ1 l :=
  alternate_bounds_snoc emptyPhi (890156643/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_10_03_φ2 : Fin 2 → ℝ := Fin.snoc half_10_03_φ1 (410859763/5000000000 : ℝ)

private theorem half_10_03_total2 : total half_10_03_φ2=(1711876169/10000000000 : ℝ) := by
  change total (Fin.snoc half_10_03_φ1 (410859763/5000000000 : ℝ))=(1711876169/10000000000 : ℝ)
  rw [alternate_total_snoc,half_10_03_total1]
  norm_num

private theorem half_10_03_bounds2 : ∀ l,0≤half_10_03_φ2 l ∧ half_10_03_φ2 l≤1 ∧
    0≤shiftExponents 9 half_10_03_φ2 l :=
  alternate_bounds_snoc half_10_03_φ1 (410859763/5000000000 : ℝ) half_10_03_bounds1 (by norm_num)

private def half_10_03_φ3 : Fin 3 → ℝ := Fin.snoc half_10_03_φ2 (717628557/10000000000 : ℝ)

private theorem half_10_03_total3 : total half_10_03_φ3=(1214752363/5000000000 : ℝ) := by
  change total (Fin.snoc half_10_03_φ2 (717628557/10000000000 : ℝ))=(1214752363/5000000000 : ℝ)
  rw [alternate_total_snoc,half_10_03_total2]
  norm_num

private theorem half_10_03_bounds3 : ∀ l,0≤half_10_03_φ3 l ∧ half_10_03_φ3 l≤1 ∧
    0≤shiftExponents 9 half_10_03_φ3 l :=
  alternate_bounds_snoc half_10_03_φ2 (717628557/10000000000 : ℝ) half_10_03_bounds2 (by norm_num)

private def half_10_03_φ4 : Fin 4 → ℝ := Fin.snoc half_10_03_φ3 (452338227/10000000000 : ℝ)

private theorem half_10_03_total4 : total half_10_03_φ4=(2881842953/10000000000 : ℝ) := by
  change total (Fin.snoc half_10_03_φ3 (452338227/10000000000 : ℝ))=(2881842953/10000000000 : ℝ)
  rw [alternate_total_snoc,half_10_03_total3]
  norm_num

private theorem half_10_03_bounds4 : ∀ l,0≤half_10_03_φ4 l ∧ half_10_03_φ4 l≤1 ∧
    0≤shiftExponents 9 half_10_03_φ4 l :=
  alternate_bounds_snoc half_10_03_φ3 (452338227/10000000000 : ℝ) half_10_03_bounds3 (by norm_num)

private theorem half_10_03_prefix : PrefixCondition 9 half_10_03_φ4 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_10_03_φ1, half_10_03_φ2, half_10_03_φ3, half_10_03_φ4, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_10_03_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 16 half_10_03_φ4) (8854471141/1250000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 9) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_03_φ4
    (fun i => (half_10_03_bounds4 i).1) (fun i => (half_10_03_bounds4 i).2.1)
    (fun i => (half_10_03_bounds4 i).2.2) half_10_03_prefix
  convert h using 1 <;> norm_num [half_10_03_total1, half_10_03_total2, half_10_03_total3, half_10_03_total4, parameterExponent, curveLoss, dyadicExponent]

private theorem half_10_03_hx4 : SourcePowerBound
    (powerBoxCross 9 6 16 half_10_03_φ4) (4311289861/625000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 6) (r := 2) (v := 0) (w := 8) (D := 16)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_10_03_φ4 (by norm_num [half_10_03_total1, half_10_03_total2, half_10_03_total3, half_10_03_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_10_03_total1, half_10_03_total2, half_10_03_total3, half_10_03_total4, parameterExponent, curveLoss, dyadicExponent]) half_10_03_hF2
    (admissibleExponent_zero 9) (SeedCompletionHigher9SimpleSeeds.degree9_half_8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_03_total1, half_10_03_total2, half_10_03_total3, half_10_03_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_10_03_hx3 : SourcePowerBound
    (powerBoxCross 9 7 8 half_10_03_φ3) (39306701109/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 7) (u := 5) (t := 8)
    (D := 8) (ψ := (452338227/10000000000 : ℝ)) half_10_03_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_10_03_bounds3 l).1) (fun l => (half_10_03_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_10_03_total1, half_10_03_total2, half_10_03_total3, half_10_03_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_6) (SeedCompletionHigher9SimpleSeeds.degree9_half_8)
    (by simpa only [half_10_03_φ4, show (2:ℝ)*8=16 by norm_num] using half_10_03_hx4)
  exact h.weaken (by norm_num [half_10_03_total1, half_10_03_total2, half_10_03_total3, half_10_03_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_10_03_hx2 : SourcePowerBound
    (powerBoxCross 9 8 4 half_10_03_φ2) (93299002629/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (717628557/10000000000 : ℝ)) half_10_03_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_10_03_bounds2 l).1) (fun l => (half_10_03_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_10_03_total1, half_10_03_total2, half_10_03_total3, half_10_03_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_7) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_10_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_03_hx3)
  exact h.weaken (by norm_num [half_10_03_total1, half_10_03_total2, half_10_03_total3, half_10_03_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_10_03_hx1 : SourcePowerBound
    (powerBoxCross 9 9 2 half_10_03_φ1) (56198304867/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (410859763/5000000000 : ℝ)) half_10_03_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_10_03_bounds1 l).1) (fun l => (half_10_03_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_10_03_total1, half_10_03_total2, half_10_03_total3, half_10_03_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_02)
    (by simpa only [half_10_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_03_hx2)
  exact h.weaken (by norm_num [half_10_03_total1, half_10_03_total2, half_10_03_total3, half_10_03_total4, parameterExponent, curveLoss, dyadicExponent])

theorem half_10_03 : AdmissibleExponent 9 20 (25505854533/2000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 8) (ψ := (890156643/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_10_03_φ1] using half_10_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_03_total1, half_10_03_total2, half_10_03_total3, half_10_03_total4, parameterExponent, curveLoss, dyadicExponent])

private def half_11_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (233063227/2500000000 : ℝ)

private theorem half_11_03_total1 : total half_11_03_φ1=(233063227/2500000000 : ℝ) := by
  norm_num [half_11_03_φ1,total,emptyPhi,Fin.snoc]

private theorem half_11_03_bounds1 : ∀ l,0≤half_11_03_φ1 l ∧ half_11_03_φ1 l≤1 ∧
    0≤shiftExponents 9 half_11_03_φ1 l :=
  alternate_bounds_snoc emptyPhi (233063227/2500000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_11_03_φ2 : Fin 2 → ℝ := Fin.snoc half_11_03_φ1 (868920803/10000000000 : ℝ)

private theorem half_11_03_total2 : total half_11_03_φ2=(1801173711/10000000000 : ℝ) := by
  change total (Fin.snoc half_11_03_φ1 (868920803/10000000000 : ℝ))=(1801173711/10000000000 : ℝ)
  rw [alternate_total_snoc,half_11_03_total1]
  norm_num

private theorem half_11_03_bounds2 : ∀ l,0≤half_11_03_φ2 l ∧ half_11_03_φ2 l≤1 ∧
    0≤shiftExponents 9 half_11_03_φ2 l :=
  alternate_bounds_snoc half_11_03_φ1 (868920803/10000000000 : ℝ) half_11_03_bounds1 (by norm_num)

private def half_11_03_φ3 : Fin 3 → ℝ := Fin.snoc half_11_03_φ2 (789780867/10000000000 : ℝ)

private theorem half_11_03_total3 : total half_11_03_φ3=(1295477289/5000000000 : ℝ) := by
  change total (Fin.snoc half_11_03_φ2 (789780867/10000000000 : ℝ))=(1295477289/5000000000 : ℝ)
  rw [alternate_total_snoc,half_11_03_total2]
  norm_num

private theorem half_11_03_bounds3 : ∀ l,0≤half_11_03_φ3 l ∧ half_11_03_φ3 l≤1 ∧
    0≤shiftExponents 9 half_11_03_φ3 l :=
  alternate_bounds_snoc half_11_03_φ2 (789780867/10000000000 : ℝ) half_11_03_bounds2 (by norm_num)

private def half_11_03_φ4 : Fin 4 → ℝ := Fin.snoc half_11_03_φ3 (315066027/5000000000 : ℝ)

private theorem half_11_03_total4 : total half_11_03_φ4=(402635829/1250000000 : ℝ) := by
  change total (Fin.snoc half_11_03_φ3 (315066027/5000000000 : ℝ))=(402635829/1250000000 : ℝ)
  rw [alternate_total_snoc,half_11_03_total3]
  norm_num

private theorem half_11_03_bounds4 : ∀ l,0≤half_11_03_φ4 l ∧ half_11_03_φ4 l≤1 ∧
    0≤shiftExponents 9 half_11_03_φ4 l :=
  alternate_bounds_snoc half_11_03_φ3 (315066027/5000000000 : ℝ) half_11_03_bounds3 (by norm_num)

private theorem half_11_03_prefix : PrefixCondition 9 half_11_03_φ4 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_11_03_φ1, half_11_03_φ2, half_11_03_φ3, half_11_03_φ4, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_11_03_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 16 half_11_03_φ4) (979592513/156250000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 9) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_03_φ4
    (fun i => (half_11_03_bounds4 i).1) (fun i => (half_11_03_bounds4 i).2.1)
    (fun i => (half_11_03_bounds4 i).2.2) half_11_03_prefix
  convert h using 1 <;> norm_num [half_11_03_total1, half_11_03_total2, half_11_03_total3, half_11_03_total4, parameterExponent, curveLoss, dyadicExponent]

private theorem half_11_03_hx4 : SourcePowerBound
    (powerBoxCross 9 7 16 half_11_03_φ4) (75053257329/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 7) (r := 2) (v := 9) (w := 10) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_11_03_φ4 (by norm_num [half_11_03_total1, half_11_03_total2, half_11_03_total3, half_11_03_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_11_03_total1, half_11_03_total2, half_11_03_total3, half_11_03_total4, parameterExponent, curveLoss, dyadicExponent]) half_11_03_hF2
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_10_03)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_03_total1, half_11_03_total2, half_11_03_total3, half_11_03_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_11_03_hx3 : SourcePowerBound
    (powerBoxCross 9 8 8 half_11_03_φ3) (17096938/1953125 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (315066027/5000000000 : ℝ)) half_11_03_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_11_03_bounds3 l).1) (fun l => (half_11_03_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_11_03_total1, half_11_03_total2, half_11_03_total3, half_11_03_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_7) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_11_03_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_03_hx4)
  exact h.weaken (by norm_num [half_11_03_total1, half_11_03_total2, half_11_03_total3, half_11_03_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_11_03_hx2 : SourcePowerBound
    (powerBoxCross 9 9 4 half_11_03_φ2) (52383170303/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (789780867/10000000000 : ℝ)) half_11_03_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_11_03_bounds2 l).1) (fun l => (half_11_03_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_11_03_total1, half_11_03_total2, half_11_03_total3, half_11_03_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_03)
    (by simpa only [half_11_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_03_hx3)
  exact h.weaken (by norm_num [half_11_03_total1, half_11_03_total2, half_11_03_total3, half_11_03_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_11_03_hx1 : SourcePowerBound
    (powerBoxCross 9 10 2 half_11_03_φ1) (7910785753/625000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (868920803/10000000000 : ℝ)) half_11_03_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_11_03_bounds1 l).1) (fun l => (half_11_03_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_11_03_total1, half_11_03_total2, half_11_03_total3, half_11_03_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_02)
    (by simpa only [half_11_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_03_hx2)
  exact h.weaken (by norm_num [half_11_03_total1, half_11_03_total2, half_11_03_total3, half_11_03_total4, parameterExponent, curveLoss, dyadicExponent])

theorem half_11_03 : AdmissibleExponent 9 22 (1442853773/100000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 9) (ψ := (233063227/2500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_10_03)
    (by simpa only [half_11_03_φ1] using half_11_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_03_total1, half_11_03_total2, half_11_03_total3, half_11_03_total4, parameterExponent, curveLoss, dyadicExponent])

private def half_12_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (241107993/2500000000 : ℝ)

private theorem half_12_03_total1 : total half_12_03_φ1=(241107993/2500000000 : ℝ) := by
  norm_num [half_12_03_φ1,total,emptyPhi,Fin.snoc]

private theorem half_12_03_bounds1 : ∀ l,0≤half_12_03_φ1 l ∧ half_12_03_φ1 l≤1 ∧
    0≤shiftExponents 9 half_12_03_φ1 l :=
  alternate_bounds_snoc emptyPhi (241107993/2500000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_12_03_φ2 : Fin 2 → ℝ := Fin.snoc half_12_03_φ1 (906522539/10000000000 : ℝ)

private theorem half_12_03_total2 : total half_12_03_φ2=(1870954511/10000000000 : ℝ) := by
  change total (Fin.snoc half_12_03_φ1 (906522539/10000000000 : ℝ))=(1870954511/10000000000 : ℝ)
  rw [alternate_total_snoc,half_12_03_total1]
  norm_num

private theorem half_12_03_bounds2 : ∀ l,0≤half_12_03_φ2 l ∧ half_12_03_φ2 l≤1 ∧
    0≤shiftExponents 9 half_12_03_φ2 l :=
  alternate_bounds_snoc half_12_03_φ1 (906522539/10000000000 : ℝ) half_12_03_bounds1 (by norm_num)

private def half_12_03_φ3 : Fin 3 → ℝ := Fin.snoc half_12_03_φ2 (843967883/10000000000 : ℝ)

private theorem half_12_03_total3 : total half_12_03_φ3=(1357461197/5000000000 : ℝ) := by
  change total (Fin.snoc half_12_03_φ2 (843967883/10000000000 : ℝ))=(1357461197/5000000000 : ℝ)
  rw [alternate_total_snoc,half_12_03_total2]
  norm_num

private theorem half_12_03_bounds3 : ∀ l,0≤half_12_03_φ3 l ∧ half_12_03_φ3 l≤1 ∧
    0≤shiftExponents 9 half_12_03_φ3 l :=
  alternate_bounds_snoc half_12_03_φ2 (843967883/10000000000 : ℝ) half_12_03_bounds2 (by norm_num)

private def half_12_03_φ4 : Fin 4 → ℝ := Fin.snoc half_12_03_φ3 (364911059/5000000000 : ℝ)

private theorem half_12_03_total4 : total half_12_03_φ4=(53824133/156250000 : ℝ) := by
  change total (Fin.snoc half_12_03_φ3 (364911059/5000000000 : ℝ))=(53824133/156250000 : ℝ)
  rw [alternate_total_snoc,half_12_03_total3]
  norm_num

private theorem half_12_03_bounds4 : ∀ l,0≤half_12_03_φ4 l ∧ half_12_03_φ4 l≤1 ∧
    0≤shiftExponents 9 half_12_03_φ4 l :=
  alternate_bounds_snoc half_12_03_φ3 (364911059/5000000000 : ℝ) half_12_03_bounds3 (by norm_num)

private def half_12_03_φ5 : Fin 5 → ℝ := Fin.snoc half_12_03_φ4 (228164003/5000000000 : ℝ)

private theorem half_12_03_total5 : total half_12_03_φ5=(1950536259/5000000000 : ℝ) := by
  change total (Fin.snoc half_12_03_φ4 (228164003/5000000000 : ℝ))=(1950536259/5000000000 : ℝ)
  rw [alternate_total_snoc,half_12_03_total4]
  norm_num

private theorem half_12_03_bounds5 : ∀ l,0≤half_12_03_φ5 l ∧ half_12_03_φ5 l≤1 ∧
    0≤shiftExponents 9 half_12_03_φ5 l :=
  alternate_bounds_snoc half_12_03_φ4 (228164003/5000000000 : ℝ) half_12_03_bounds4 (by norm_num)

private theorem half_12_03_prefix : PrefixCondition 9 half_12_03_φ5 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_12_03_φ1, half_12_03_φ2, half_12_03_φ3, half_12_03_φ4, half_12_03_φ5, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_12_03_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 32 half_12_03_φ5) (4773391223/625000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_12_03_φ5
    (fun i => (half_12_03_bounds5 i).1) (fun i => (half_12_03_bounds5 i).2.1)
    (fun i => (half_12_03_bounds5 i).2.2) half_12_03_prefix
  convert h using 1 <;> norm_num [half_12_03_total1, half_12_03_total2, half_12_03_total3, half_12_03_total4, half_12_03_total5, parameterExponent, curveLoss, dyadicExponent]

private theorem half_12_03_hx5 : SourcePowerBound
    (powerBoxCross 9 7 32 half_12_03_φ5) (18129254283/2500000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 7) (r := 2) (v := 9) (w := 10) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_12_03_φ5 (by norm_num [half_12_03_total1, half_12_03_total2, half_12_03_total3, half_12_03_total4, half_12_03_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_12_03_total1, half_12_03_total2, half_12_03_total3, half_12_03_total4, half_12_03_total5, parameterExponent, curveLoss, dyadicExponent]) half_12_03_hF2
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_10_03)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_03_total1, half_12_03_total2, half_12_03_total3, half_12_03_total4, half_12_03_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_03_hx4 : SourcePowerBound
    (powerBoxCross 9 8 16 half_12_03_φ4) (1280728721/156250000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 8) (u := 6) (t := 9)
    (D := 16) (ψ := (228164003/5000000000 : ℝ)) half_12_03_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_03_bounds4 l).1) (fun l => (half_12_03_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_03_total1, half_12_03_total2, half_12_03_total3, half_12_03_total4, half_12_03_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_7) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_12_03_φ5, show (2:ℝ)*16=32 by norm_num] using half_12_03_hx5)
  exact h.weaken (by norm_num [half_12_03_total1, half_12_03_total2, half_12_03_total3, half_12_03_total4, half_12_03_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_03_hx3 : SourcePowerBound
    (powerBoxCross 9 9 8 half_12_03_φ3) (48525163901/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (364911059/5000000000 : ℝ)) half_12_03_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_03_bounds3 l).1) (fun l => (half_12_03_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_03_total1, half_12_03_total2, half_12_03_total3, half_12_03_total4, half_12_03_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_03)
    (by simpa only [half_12_03_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_03_hx4)
  exact h.weaken (by norm_num [half_12_03_total1, half_12_03_total2, half_12_03_total3, half_12_03_total4, half_12_03_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_03_hx2 : SourcePowerBound
    (powerBoxCross 9 10 4 half_12_03_φ2) (29215048159/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (843967883/10000000000 : ℝ)) half_12_03_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_03_bounds2 l).1) (fun l => (half_12_03_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_03_total1, half_12_03_total2, half_12_03_total3, half_12_03_total4, half_12_03_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_03)
    (by simpa only [half_12_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_03_hx3)
  exact h.weaken (by norm_num [half_12_03_total1, half_12_03_total2, half_12_03_total3, half_12_03_total4, half_12_03_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_03_hx1 : SourcePowerBound
    (powerBoxCross 9 11 2 half_12_03_φ1) (28266893237/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (906522539/10000000000 : ℝ)) half_12_03_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_03_bounds1 l).1) (fun l => (half_12_03_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_03_total1, half_12_03_total2, half_12_03_total3, half_12_03_total4, half_12_03_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_03) (half_12_02)
    (by simpa only [half_12_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_03_hx2)
  exact h.weaken (by norm_num [half_12_03_total1, half_12_03_total2, half_12_03_total3, half_12_03_total4, half_12_03_total5, parameterExponent, curveLoss, dyadicExponent])

theorem half_12_03 : AdmissibleExponent 9 24 (161587537597/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 10) (ψ := (241107993/2500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_11_03)
    (by simpa only [half_12_03_φ1] using half_12_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_03_total1, half_12_03_total2, half_12_03_total3, half_12_03_total4, half_12_03_total5, parameterExponent, curveLoss, dyadicExponent])

private def half_13_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (991902627/10000000000 : ℝ)

private theorem half_13_03_total1 : total half_13_03_φ1=(991902627/10000000000 : ℝ) := by
  norm_num [half_13_03_φ1,total,emptyPhi,Fin.snoc]

private theorem half_13_03_bounds1 : ∀ l,0≤half_13_03_φ1 l ∧ half_13_03_φ1 l≤1 ∧
    0≤shiftExponents 9 half_13_03_φ1 l :=
  alternate_bounds_snoc emptyPhi (991902627/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_13_03_φ2 : Fin 2 → ℝ := Fin.snoc half_13_03_φ1 (1464183/15625000 : ℝ)

private theorem half_13_03_total2 : total half_13_03_φ2=(1928979747/10000000000 : ℝ) := by
  change total (Fin.snoc half_13_03_φ1 (1464183/15625000 : ℝ))=(1928979747/10000000000 : ℝ)
  rw [alternate_total_snoc,half_13_03_total1]
  norm_num

private theorem half_13_03_bounds2 : ∀ l,0≤half_13_03_φ2 l ∧ half_13_03_φ2 l≤1 ∧
    0≤shiftExponents 9 half_13_03_φ2 l :=
  alternate_bounds_snoc half_13_03_φ1 (1464183/15625000 : ℝ) half_13_03_bounds1 (by norm_num)

private def half_13_03_φ3 : Fin 3 → ℝ := Fin.snoc half_13_03_φ2 (443397339/5000000000 : ℝ)

private theorem half_13_03_total3 : total half_13_03_φ3=(112630977/400000000 : ℝ) := by
  change total (Fin.snoc half_13_03_φ2 (443397339/5000000000 : ℝ))=(112630977/400000000 : ℝ)
  rw [alternate_total_snoc,half_13_03_total2]
  norm_num

private theorem half_13_03_bounds3 : ∀ l,0≤half_13_03_φ3 l ∧ half_13_03_φ3 l≤1 ∧
    0≤shiftExponents 9 half_13_03_φ3 l :=
  alternate_bounds_snoc half_13_03_φ2 (443397339/5000000000 : ℝ) half_13_03_bounds2 (by norm_num)

private def half_13_03_φ4 : Fin 4 → ℝ := Fin.snoc half_13_03_φ3 (200291541/2500000000 : ℝ)

private theorem half_13_03_total4 : total half_13_03_φ4=(3616940589/10000000000 : ℝ) := by
  change total (Fin.snoc half_13_03_φ3 (200291541/2500000000 : ℝ))=(3616940589/10000000000 : ℝ)
  rw [alternate_total_snoc,half_13_03_total3]
  norm_num

private theorem half_13_03_bounds4 : ∀ l,0≤half_13_03_φ4 l ∧ half_13_03_φ4 l≤1 ∧
    0≤shiftExponents 9 half_13_03_φ4 l :=
  alternate_bounds_snoc half_13_03_φ3 (200291541/2500000000 : ℝ) half_13_03_bounds3 (by norm_num)

private def half_13_03_φ5 : Fin 5 → ℝ := Fin.snoc half_13_03_φ4 (61950103/1000000000 : ℝ)

private theorem half_13_03_total5 : total half_13_03_φ5=(4236441619/10000000000 : ℝ) := by
  change total (Fin.snoc half_13_03_φ4 (61950103/1000000000 : ℝ))=(4236441619/10000000000 : ℝ)
  rw [alternate_total_snoc,half_13_03_total4]
  norm_num

private theorem half_13_03_bounds5 : ∀ l,0≤half_13_03_φ5 l ∧ half_13_03_φ5 l≤1 ∧
    0≤shiftExponents 9 half_13_03_φ5 l :=
  alternate_bounds_snoc half_13_03_φ4 (61950103/1000000000 : ℝ) half_13_03_bounds4 (by norm_num)

private theorem half_13_03_prefix : PrefixCondition 9 half_13_03_φ5 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_13_03_φ1, half_13_03_φ2, half_13_03_φ3, half_13_03_φ4, half_13_03_φ5, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_13_03_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 32 half_13_03_φ5) (8540675143/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_13_03_φ5
    (fun i => (half_13_03_bounds5 i).1) (fun i => (half_13_03_bounds5 i).2.1)
    (fun i => (half_13_03_bounds5 i).2.2) half_13_03_prefix
  convert h using 1 <;> norm_num [half_13_03_total1, half_13_03_total2, half_13_03_total3, half_13_03_total4, half_13_03_total5, parameterExponent, curveLoss, dyadicExponent]

private theorem half_13_03_hx5 : SourcePowerBound
    (powerBoxCross 9 8 32 half_13_03_φ5) (77036770273/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 8) (r := 2) (v := 10) (w := 11) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_13_03_φ5 (by norm_num [half_13_03_total1, half_13_03_total2, half_13_03_total3, half_13_03_total4, half_13_03_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_13_03_total1, half_13_03_total2, half_13_03_total3, half_13_03_total4, half_13_03_total5, parameterExponent, curveLoss, dyadicExponent]) half_13_03_hF2
    (half_10_03) (half_11_03)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_03_total1, half_13_03_total2, half_13_03_total3, half_13_03_total4, half_13_03_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_03_hx4 : SourcePowerBound
    (powerBoxCross 9 9 16 half_13_03_φ4) (89398226709/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (61950103/1000000000 : ℝ)) half_13_03_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_03_bounds4 l).1) (fun l => (half_13_03_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_03_total1, half_13_03_total2, half_13_03_total3, half_13_03_total4, half_13_03_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_03)
    (by simpa only [half_13_03_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_03_hx5)
  exact h.weaken (by norm_num [half_13_03_total1, half_13_03_total2, half_13_03_total3, half_13_03_total4, half_13_03_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_03_hx3 : SourcePowerBound
    (powerBoxCross 9 10 8 half_13_03_φ3) (53537431467/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (200291541/2500000000 : ℝ)) half_13_03_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_03_bounds3 l).1) (fun l => (half_13_03_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_03_total1, half_13_03_total2, half_13_03_total3, half_13_03_total4, half_13_03_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_03)
    (by simpa only [half_13_03_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_03_hx4)
  exact h.weaken (by norm_num [half_13_03_total1, half_13_03_total2, half_13_03_total3, half_13_03_total4, half_13_03_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_03_hx2 : SourcePowerBound
    (powerBoxCross 9 11 4 half_13_03_φ2) (129454876349/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (443397339/5000000000 : ℝ)) half_13_03_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_03_bounds2 l).1) (fun l => (half_13_03_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_03_total1, half_13_03_total2, half_13_03_total3, half_13_03_total4, half_13_03_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_03) (half_12_03)
    (by simpa only [half_13_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_03_hx3)
  exact h.weaken (by norm_num [half_13_03_total1, half_13_03_total2, half_13_03_total3, half_13_03_total4, half_13_03_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_03_hx1 : SourcePowerBound
    (powerBoxCross 9 12 2 half_13_03_φ1) (6262061197/400000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (1464183/15625000 : ℝ)) half_13_03_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_03_bounds1 l).1) (fun l => (half_13_03_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_03_total1, half_13_03_total2, half_13_03_total3, half_13_03_total4, half_13_03_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_03) (half_13_02)
    (by simpa only [half_13_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_03_hx2)
  exact h.weaken (by norm_num [half_13_03_total1, half_13_03_total2, half_13_03_total3, half_13_03_total4, half_13_03_total5, parameterExponent, curveLoss, dyadicExponent])

theorem half_13_03 : AdmissibleExponent 9 26 (89682645173/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 11) (ψ := (991902627/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_12_03)
    (by simpa only [half_13_03_φ1] using half_13_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_03_total1, half_13_03_total2, half_13_03_total3, half_13_03_total4, half_13_03_total5, parameterExponent, curveLoss, dyadicExponent])

theorem chord_62 : AdmissibleExponent 9 28 (197900367629/10000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 28) (t := (1/2 : ℝ))
    (half_13_03) (half_15_02)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_14_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1013562279/10000000000 : ℝ)

private theorem half_14_03_total1 : total half_14_03_φ1=(1013562279/10000000000 : ℝ) := by
  norm_num [half_14_03_φ1,total,emptyPhi,Fin.snoc]

private theorem half_14_03_bounds1 : ∀ l,0≤half_14_03_φ1 l ∧ half_14_03_φ1 l≤1 ∧
    0≤shiftExponents 9 half_14_03_φ1 l :=
  alternate_bounds_snoc emptyPhi (1013562279/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_14_03_φ2 : Fin 2 → ℝ := Fin.snoc half_14_03_φ1 (482292981/5000000000 : ℝ)

private theorem half_14_03_total2 : total half_14_03_φ2=(1978148241/10000000000 : ℝ) := by
  change total (Fin.snoc half_14_03_φ1 (482292981/5000000000 : ℝ))=(1978148241/10000000000 : ℝ)
  rw [alternate_total_snoc,half_14_03_total1]
  norm_num

private theorem half_14_03_bounds2 : ∀ l,0≤half_14_03_φ2 l ∧ half_14_03_φ2 l≤1 ∧
    0≤shiftExponents 9 half_14_03_φ2 l :=
  alternate_bounds_snoc half_14_03_φ1 (482292981/5000000000 : ℝ) half_14_03_bounds1 (by norm_num)

private def half_14_03_φ3 : Fin 3 → ℝ := Fin.snoc half_14_03_φ2 (230504817/2500000000 : ℝ)

private theorem half_14_03_total3 : total half_14_03_φ3=(2900167509/10000000000 : ℝ) := by
  change total (Fin.snoc half_14_03_φ2 (230504817/2500000000 : ℝ))=(2900167509/10000000000 : ℝ)
  rw [alternate_total_snoc,half_14_03_total2]
  norm_num

private theorem half_14_03_bounds3 : ∀ l,0≤half_14_03_φ3 l ∧ half_14_03_φ3 l≤1 ∧
    0≤shiftExponents 9 half_14_03_φ3 l :=
  alternate_bounds_snoc half_14_03_φ2 (230504817/2500000000 : ℝ) half_14_03_bounds2 (by norm_num)

private def half_14_03_φ4 : Fin 4 → ℝ := Fin.snoc half_14_03_φ3 (171342463/2000000000 : ℝ)

private theorem half_14_03_total4 : total half_14_03_φ4=(234804989/625000000 : ℝ) := by
  change total (Fin.snoc half_14_03_φ3 (171342463/2000000000 : ℝ))=(234804989/625000000 : ℝ)
  rw [alternate_total_snoc,half_14_03_total3]
  norm_num

private theorem half_14_03_bounds4 : ∀ l,0≤half_14_03_φ4 l ∧ half_14_03_φ4 l≤1 ∧
    0≤shiftExponents 9 half_14_03_φ4 l :=
  alternate_bounds_snoc half_14_03_φ3 (171342463/2000000000 : ℝ) half_14_03_bounds3 (by norm_num)

private def half_14_03_φ5 : Fin 5 → ℝ := Fin.snoc half_14_03_φ4 (182787493/2500000000 : ℝ)

private theorem half_14_03_total5 : total half_14_03_φ5=(1122007449/2500000000 : ℝ) := by
  change total (Fin.snoc half_14_03_φ4 (182787493/2500000000 : ℝ))=(1122007449/2500000000 : ℝ)
  rw [alternate_total_snoc,half_14_03_total4]
  norm_num

private theorem half_14_03_bounds5 : ∀ l,0≤half_14_03_φ5 l ∧ half_14_03_φ5 l≤1 ∧
    0≤shiftExponents 9 half_14_03_φ5 l :=
  alternate_bounds_snoc half_14_03_φ4 (182787493/2500000000 : ℝ) half_14_03_bounds4 (by norm_num)

private def half_14_03_φ6 : Fin 6 → ℝ := Fin.snoc half_14_03_φ5 (54030601/1250000000 : ℝ)

private theorem half_14_03_total6 : total half_14_03_φ6=(1230068651/2500000000 : ℝ) := by
  change total (Fin.snoc half_14_03_φ5 (54030601/1250000000 : ℝ))=(1230068651/2500000000 : ℝ)
  rw [alternate_total_snoc,half_14_03_total5]
  norm_num

private theorem half_14_03_bounds6 : ∀ l,0≤half_14_03_φ6 l ∧ half_14_03_φ6 l≤1 ∧
    0≤shiftExponents 9 half_14_03_φ6 l :=
  alternate_bounds_snoc half_14_03_φ5 (54030601/1250000000 : ℝ) half_14_03_bounds5 (by norm_num)

private theorem half_14_03_prefix : PrefixCondition 9 half_14_03_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_14_03_φ1, half_14_03_φ2, half_14_03_φ3, half_14_03_φ4, half_14_03_φ5, half_14_03_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_14_03_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_14_03_φ6) (2559794047/312500000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_14_03_φ6
    (fun i => (half_14_03_bounds6 i).1) (fun i => (half_14_03_bounds6 i).2.1)
    (fun i => (half_14_03_bounds6 i).2.2) half_14_03_prefix
  convert h using 1 <;> norm_num [half_14_03_total1, half_14_03_total2, half_14_03_total3, half_14_03_total4, half_14_03_total5, half_14_03_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_14_03_hF1 : SourcePowerBound
    (paddedMoment 9 0 1 64 half_14_03_φ6) (957431349/312500000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_14_03_φ6
    (fun i => (half_14_03_bounds6 i).1) (fun i => (half_14_03_bounds6 i).2.1)
    (fun i => (half_14_03_bounds6 i).2.2) half_14_03_prefix
  convert h using 1 <;> norm_num [half_14_03_total1, half_14_03_total2, half_14_03_total3, half_14_03_total4, half_14_03_total5, half_14_03_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_14_03_hx6 : SourcePowerBound
    (powerBoxCross 9 8 64 half_14_03_φ6) (73313318329/10000000000 : ℝ) := by
  have h := full_B_cross_power (k := 9) (s := 8) (r := 1) (v := 2) (t := 11) (D := 64)
    (a := (1/22 : ℝ)) (b := (5/22 : ℝ)) (c := (8/11 : ℝ))
    (by norm_num) half_14_03_φ6 (by norm_num [half_14_03_total1, half_14_03_total2, half_14_03_total3, half_14_03_total4, half_14_03_total5, half_14_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_14_03_total1, half_14_03_total2, half_14_03_total3, half_14_03_total4, half_14_03_total5, half_14_03_total6, parameterExponent, curveLoss, dyadicExponent]) half_14_03_hF1 half_14_03_hF2
    (half_11_03)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_03_total1, half_14_03_total2, half_14_03_total3, half_14_03_total4, half_14_03_total5, half_14_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_03_hx5 : SourcePowerBound
    (powerBoxCross 9 9 32 half_14_03_φ5) (41046626797/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 9) (u := 7) (t := 10)
    (D := 32) (ψ := (54030601/1250000000 : ℝ)) half_14_03_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_03_bounds5 l).1) (fun l => (half_14_03_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_03_total1, half_14_03_total2, half_14_03_total3, half_14_03_total4, half_14_03_total5, half_14_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_03)
    (by simpa only [half_14_03_φ6, show (2:ℝ)*32=64 by norm_num] using half_14_03_hx6)
  exact h.weaken (by norm_num [half_14_03_total1, half_14_03_total2, half_14_03_total3, half_14_03_total4, half_14_03_total5, half_14_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_03_hx4 : SourcePowerBound
    (powerBoxCross 9 10 16 half_14_03_φ4) (9727342977/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (182787493/2500000000 : ℝ)) half_14_03_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_03_bounds4 l).1) (fun l => (half_14_03_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_03_total1, half_14_03_total2, half_14_03_total3, half_14_03_total4, half_14_03_total5, half_14_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_03)
    (by simpa only [half_14_03_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_03_hx5)
  exact h.weaken (by norm_num [half_14_03_total1, half_14_03_total2, half_14_03_total3, half_14_03_total4, half_14_03_total5, half_14_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_03_hx3 : SourcePowerBound
    (powerBoxCross 9 11 8 half_14_03_φ3) (117537034321/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (171342463/2000000000 : ℝ)) half_14_03_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_03_bounds3 l).1) (fun l => (half_14_03_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_03_total1, half_14_03_total2, half_14_03_total3, half_14_03_total4, half_14_03_total5, half_14_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_03) (half_12_03)
    (by simpa only [half_14_03_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_03_hx4)
  exact h.weaken (by norm_num [half_14_03_total1, half_14_03_total2, half_14_03_total3, half_14_03_total4, half_14_03_total5, half_14_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_03_hx2 : SourcePowerBound
    (powerBoxCross 9 12 4 half_14_03_φ2) (35619803751/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (230504817/2500000000 : ℝ)) half_14_03_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_03_bounds2 l).1) (fun l => (half_14_03_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_03_total1, half_14_03_total2, half_14_03_total3, half_14_03_total4, half_14_03_total5, half_14_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_03) (half_13_03)
    (by simpa only [half_14_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_03_hx3)
  exact h.weaken (by norm_num [half_14_03_total1, half_14_03_total2, half_14_03_total3, half_14_03_total4, half_14_03_total5, half_14_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_03_hx1 : SourcePowerBound
    (powerBoxCross 9 13 2 half_14_03_φ1) (172199063383/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (482292981/5000000000 : ℝ)) half_14_03_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_03_bounds1 l).1) (fun l => (half_14_03_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_03_total1, half_14_03_total2, half_14_03_total3, half_14_03_total4, half_14_03_total5, half_14_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_03) (chord_62)
    (by simpa only [half_14_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_03_hx2)
  exact h.weaken (by norm_num [half_14_03_total1, half_14_03_total2, half_14_03_total3, half_14_03_total4, half_14_03_total5, half_14_03_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_14_03 : AdmissibleExponent 9 28 (98769060179/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 12) (ψ := (1013562279/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_13_03)
    (by simpa only [half_14_03_φ1] using half_14_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_03_total1, half_14_03_total2, half_14_03_total3, half_14_03_total4, half_14_03_total5, half_14_03_total6, parameterExponent, curveLoss, dyadicExponent])

theorem chord_63 : AdmissibleExponent 9 30 (432766948561/20000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 30) (t := (1/2 : ℝ))
    (half_14_03) (half_16_02)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_15_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1031458523/10000000000 : ℝ)

private theorem half_15_03_total1 : total half_15_03_φ1=(1031458523/10000000000 : ℝ) := by
  norm_num [half_15_03_φ1,total,emptyPhi,Fin.snoc]

private theorem half_15_03_bounds1 : ∀ l,0≤half_15_03_φ1 l ∧ half_15_03_φ1 l≤1 ∧
    0≤shiftExponents 9 half_15_03_φ1 l :=
  alternate_bounds_snoc emptyPhi (1031458523/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_15_03_φ2 : Fin 2 → ℝ := Fin.snoc half_15_03_φ1 (987552083/10000000000 : ℝ)

private theorem half_15_03_total2 : total half_15_03_φ2=(1009505303/5000000000 : ℝ) := by
  change total (Fin.snoc half_15_03_φ1 (987552083/10000000000 : ℝ))=(1009505303/5000000000 : ℝ)
  rw [alternate_total_snoc,half_15_03_total1]
  norm_num

private theorem half_15_03_bounds2 : ∀ l,0≤half_15_03_φ2 l ∧ half_15_03_φ2 l≤1 ∧
    0≤shiftExponents 9 half_15_03_φ2 l :=
  alternate_bounds_snoc half_15_03_φ1 (987552083/10000000000 : ℝ) half_15_03_bounds1 (by norm_num)

private def half_15_03_φ3 : Fin 3 → ℝ := Fin.snoc half_15_03_φ2 (951459313/10000000000 : ℝ)

private theorem half_15_03_total3 : total half_15_03_φ3=(2970469919/10000000000 : ℝ) := by
  change total (Fin.snoc half_15_03_φ2 (951459313/10000000000 : ℝ))=(2970469919/10000000000 : ℝ)
  rw [alternate_total_snoc,half_15_03_total2]
  norm_num

private theorem half_15_03_bounds3 : ∀ l,0≤half_15_03_φ3 l ∧ half_15_03_φ3 l≤1 ∧
    0≤shiftExponents 9 half_15_03_φ3 l :=
  alternate_bounds_snoc half_15_03_φ2 (951459313/10000000000 : ℝ) half_15_03_bounds2 (by norm_num)

private def half_15_03_φ4 : Fin 4 → ℝ := Fin.snoc half_15_03_φ3 (878691259/10000000000 : ℝ)

private theorem half_15_03_total4 : total half_15_03_φ4=(1924580589/5000000000 : ℝ) := by
  change total (Fin.snoc half_15_03_φ3 (878691259/10000000000 : ℝ))=(1924580589/5000000000 : ℝ)
  rw [alternate_total_snoc,half_15_03_total3]
  norm_num

private theorem half_15_03_bounds4 : ∀ l,0≤half_15_03_φ4 l ∧ half_15_03_φ4 l≤1 ∧
    0≤shiftExponents 9 half_15_03_φ4 l :=
  alternate_bounds_snoc half_15_03_φ3 (878691259/10000000000 : ℝ) half_15_03_bounds3 (by norm_num)

private def half_15_03_φ5 : Fin 5 → ℝ := Fin.snoc half_15_03_φ4 (192213713/2500000000 : ℝ)

private theorem half_15_03_total5 : total half_15_03_φ5=(461801603/1000000000 : ℝ) := by
  change total (Fin.snoc half_15_03_φ4 (192213713/2500000000 : ℝ))=(461801603/1000000000 : ℝ)
  rw [alternate_total_snoc,half_15_03_total4]
  norm_num

private theorem half_15_03_bounds5 : ∀ l,0≤half_15_03_φ5 l ∧ half_15_03_φ5 l≤1 ∧
    0≤shiftExponents 9 half_15_03_φ5 l :=
  alternate_bounds_snoc half_15_03_φ4 (192213713/2500000000 : ℝ) half_15_03_bounds4 (by norm_num)

private def half_15_03_φ6 : Fin 6 → ℝ := Fin.snoc half_15_03_φ5 (281567213/5000000000 : ℝ)

private theorem half_15_03_total6 : total half_15_03_φ6=(647643807/1250000000 : ℝ) := by
  change total (Fin.snoc half_15_03_φ5 (281567213/5000000000 : ℝ))=(647643807/1250000000 : ℝ)
  rw [alternate_total_snoc,half_15_03_total5]
  norm_num

private theorem half_15_03_bounds6 : ∀ l,0≤half_15_03_φ6 l ∧ half_15_03_φ6 l≤1 ∧
    0≤shiftExponents 9 half_15_03_φ6 l :=
  alternate_bounds_snoc half_15_03_φ5 (281567213/5000000000 : ℝ) half_15_03_bounds5 (by norm_num)

private theorem half_15_03_prefix : PrefixCondition 9 half_15_03_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_15_03_φ1, half_15_03_φ2, half_15_03_φ3, half_15_03_φ4, half_15_03_φ5, half_15_03_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_15_03_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_15_03_φ6) (1182068579/156250000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_15_03_φ6
    (fun i => (half_15_03_bounds6 i).1) (fun i => (half_15_03_bounds6 i).2.1)
    (fun i => (half_15_03_bounds6 i).2.2) half_15_03_prefix
  convert h using 1 <;> norm_num [half_15_03_total1, half_15_03_total2, half_15_03_total3, half_15_03_total4, half_15_03_total5, half_15_03_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_15_03_hx6 : SourcePowerBound
    (powerBoxCross 9 9 64 half_15_03_φ6) (38656524827/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 9) (r := 2) (v := 0) (w := 12) (D := 64)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_15_03_φ6 (by norm_num [half_15_03_total1, half_15_03_total2, half_15_03_total3, half_15_03_total4, half_15_03_total5, half_15_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_15_03_total1, half_15_03_total2, half_15_03_total3, half_15_03_total4, half_15_03_total5, half_15_03_total6, parameterExponent, curveLoss, dyadicExponent]) half_15_03_hF2
    (admissibleExponent_zero 9) (half_12_03)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_03_total1, half_15_03_total2, half_15_03_total3, half_15_03_total4, half_15_03_total5, half_15_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_03_hx5 : SourcePowerBound
    (powerBoxCross 9 10 32 half_15_03_φ5) (17759636543/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 10) (u := 8) (t := 11)
    (D := 32) (ψ := (281567213/5000000000 : ℝ)) half_15_03_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_03_bounds5 l).1) (fun l => (half_15_03_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_03_total1, half_15_03_total2, half_15_03_total3, half_15_03_total4, half_15_03_total5, half_15_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_03)
    (by simpa only [half_15_03_φ6, show (2:ℝ)*32=64 by norm_num] using half_15_03_hx6)
  exact h.weaken (by norm_num [half_15_03_total1, half_15_03_total2, half_15_03_total3, half_15_03_total4, half_15_03_total5, half_15_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_03_hx4 : SourcePowerBound
    (powerBoxCross 9 11 16 half_15_03_φ4) (10600151271/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (192213713/2500000000 : ℝ)) half_15_03_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_03_bounds4 l).1) (fun l => (half_15_03_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_03_total1, half_15_03_total2, half_15_03_total3, half_15_03_total4, half_15_03_total5, half_15_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_03) (half_12_03)
    (by simpa only [half_15_03_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_03_hx5)
  exact h.weaken (by norm_num [half_15_03_total1, half_15_03_total2, half_15_03_total3, half_15_03_total4, half_15_03_total5, half_15_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_03_hx3 : SourcePowerBound
    (powerBoxCross 9 12 8 half_15_03_φ3) (64193910049/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (878691259/10000000000 : ℝ)) half_15_03_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_03_bounds3 l).1) (fun l => (half_15_03_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_03_total1, half_15_03_total2, half_15_03_total3, half_15_03_total4, half_15_03_total5, half_15_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_03) (half_13_03)
    (by simpa only [half_15_03_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_03_hx4)
  exact h.weaken (by norm_num [half_15_03_total1, half_15_03_total2, half_15_03_total3, half_15_03_total4, half_15_03_total5, half_15_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_03_hx2 : SourcePowerBound
    (powerBoxCross 9 13 4 half_15_03_φ2) (155887131899/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (951459313/10000000000 : ℝ)) half_15_03_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_03_bounds2 l).1) (fun l => (half_15_03_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_03_total1, half_15_03_total2, half_15_03_total3, half_15_03_total4, half_15_03_total5, half_15_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_03) (half_14_03)
    (by simpa only [half_15_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_03_hx3)
  exact h.weaken (by norm_num [half_15_03_total1, half_15_03_total2, half_15_03_total3, half_15_03_total4, half_15_03_total5, half_15_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_03_hx1 : SourcePowerBound
    (powerBoxCross 9 14 2 half_15_03_φ1) (188194341097/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (987552083/10000000000 : ℝ)) half_15_03_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_03_bounds1 l).1) (fun l => (half_15_03_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_03_total1, half_15_03_total2, half_15_03_total3, half_15_03_total4, half_15_03_total5, half_15_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_03) (chord_63)
    (by simpa only [half_15_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_03_hx2)
  exact h.weaken (by norm_num [half_15_03_total1, half_15_03_total2, half_15_03_total3, half_15_03_total4, half_15_03_total5, half_15_03_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_15_03 : AdmissibleExponent 9 30 (108021860609/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 13) (ψ := (1031458523/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_14_03)
    (by simpa only [half_15_03_φ1] using half_15_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_03_total1, half_15_03_total2, half_15_03_total3, half_15_03_total4, half_15_03_total5, half_15_03_total6, parameterExponent, curveLoss, dyadicExponent])

theorem chord_64 : AdmissibleExponent 9 32 (23515373397/1000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 32) (t := (1/2 : ℝ))
    (half_15_03) (half_17_02)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_16_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (524112713/5000000000 : ℝ)

private theorem half_16_03_total1 : total half_16_03_φ1=(524112713/5000000000 : ℝ) := by
  norm_num [half_16_03_φ1,total,emptyPhi,Fin.snoc]

private theorem half_16_03_bounds1 : ∀ l,0≤half_16_03_φ1 l ∧ half_16_03_φ1 l≤1 ∧
    0≤shiftExponents 9 half_16_03_φ1 l :=
  alternate_bounds_snoc emptyPhi (524112713/5000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_16_03_φ2 : Fin 2 → ℝ := Fin.snoc half_16_03_φ1 (1009800141/10000000000 : ℝ)

private theorem half_16_03_total2 : total half_16_03_φ2=(2058025567/10000000000 : ℝ) := by
  change total (Fin.snoc half_16_03_φ1 (1009800141/10000000000 : ℝ))=(2058025567/10000000000 : ℝ)
  rw [alternate_total_snoc,half_16_03_total1]
  norm_num

private theorem half_16_03_bounds2 : ∀ l,0≤half_16_03_φ2 l ∧ half_16_03_φ2 l≤1 ∧
    0≤shiftExponents 9 half_16_03_φ2 l :=
  alternate_bounds_snoc half_16_03_φ1 (1009800141/10000000000 : ℝ) half_16_03_bounds1 (by norm_num)

private def half_16_03_φ3 : Fin 3 → ℝ := Fin.snoc half_16_03_φ2 (61326853/625000000 : ℝ)

private theorem half_16_03_total3 : total half_16_03_φ3=(607851043/2000000000 : ℝ) := by
  change total (Fin.snoc half_16_03_φ2 (61326853/625000000 : ℝ))=(607851043/2000000000 : ℝ)
  rw [alternate_total_snoc,half_16_03_total2]
  norm_num

private theorem half_16_03_bounds3 : ∀ l,0≤half_16_03_φ3 l ∧ half_16_03_φ3 l≤1 ∧
    0≤shiftExponents 9 half_16_03_φ3 l :=
  alternate_bounds_snoc half_16_03_φ2 (61326853/625000000 : ℝ) half_16_03_bounds2 (by norm_num)

private def half_16_03_φ4 : Fin 4 → ℝ := Fin.snoc half_16_03_φ3 (870093097/10000000000 : ℝ)

private theorem half_16_03_total4 : total half_16_03_φ4=(488668539/1250000000 : ℝ) := by
  change total (Fin.snoc half_16_03_φ3 (870093097/10000000000 : ℝ))=(488668539/1250000000 : ℝ)
  rw [alternate_total_snoc,half_16_03_total3]
  norm_num

private theorem half_16_03_bounds4 : ∀ l,0≤half_16_03_φ4 l ∧ half_16_03_φ4 l≤1 ∧
    0≤shiftExponents 9 half_16_03_φ4 l :=
  alternate_bounds_snoc half_16_03_φ3 (870093097/10000000000 : ℝ) half_16_03_bounds3 (by norm_num)

private def half_16_03_φ5 : Fin 5 → ℝ := Fin.snoc half_16_03_φ4 (38066573/500000000 : ℝ)

private theorem half_16_03_total5 : total half_16_03_φ5=(1167669943/2500000000 : ℝ) := by
  change total (Fin.snoc half_16_03_φ4 (38066573/500000000 : ℝ))=(1167669943/2500000000 : ℝ)
  rw [alternate_total_snoc,half_16_03_total4]
  norm_num

private theorem half_16_03_bounds5 : ∀ l,0≤half_16_03_φ5 l ∧ half_16_03_φ5 l≤1 ∧
    0≤shiftExponents 9 half_16_03_φ5 l :=
  alternate_bounds_snoc half_16_03_φ4 (38066573/500000000 : ℝ) half_16_03_bounds4 (by norm_num)

private def half_16_03_φ6 : Fin 6 → ℝ := Fin.snoc half_16_03_φ5 (166541257/2500000000 : ℝ)

private theorem half_16_03_total6 : total half_16_03_φ6=(416941/781250 : ℝ) := by
  change total (Fin.snoc half_16_03_φ5 (166541257/2500000000 : ℝ))=(416941/781250 : ℝ)
  rw [alternate_total_snoc,half_16_03_total5]
  norm_num

private theorem half_16_03_bounds6 : ∀ l,0≤half_16_03_φ6 l ∧ half_16_03_φ6 l≤1 ∧
    0≤shiftExponents 9 half_16_03_φ6 l :=
  alternate_bounds_snoc half_16_03_φ5 (166541257/2500000000 : ℝ) half_16_03_bounds5 (by norm_num)

private theorem half_16_03_prefix : PrefixCondition 9 half_16_03_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_16_03_φ1, half_16_03_φ2, half_16_03_φ3, half_16_03_φ4, half_16_03_φ5, half_16_03_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_16_03_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_16_03_φ6) (2809208/390625 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_16_03_φ6
    (fun i => (half_16_03_bounds6 i).1) (fun i => (half_16_03_bounds6 i).2.1)
    (fun i => (half_16_03_bounds6 i).2.2) half_16_03_prefix
  convert h using 1 <;> norm_num [half_16_03_total1, half_16_03_total2, half_16_03_total3, half_16_03_total4, half_16_03_total5, half_16_03_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_16_03_hx6 : SourcePowerBound
    (powerBoxCross 9 10 64 half_16_03_φ6) (20707028337/2500000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 10) (r := 2) (v := 13) (w := 14) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_16_03_φ6 (by norm_num [half_16_03_total1, half_16_03_total2, half_16_03_total3, half_16_03_total4, half_16_03_total5, half_16_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_16_03_total1, half_16_03_total2, half_16_03_total3, half_16_03_total4, half_16_03_total5, half_16_03_total6, parameterExponent, curveLoss, dyadicExponent]) half_16_03_hF2
    (half_13_03) (half_14_03)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_03_total1, half_16_03_total2, half_16_03_total3, half_16_03_total4, half_16_03_total5, half_16_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_03_hx5 : SourcePowerBound
    (powerBoxCross 9 11 32 half_16_03_φ5) (24279372997/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 11) (u := 9) (t := 12)
    (D := 32) (ψ := (166541257/2500000000 : ℝ)) half_16_03_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_03_bounds5 l).1) (fun l => (half_16_03_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_03_total1, half_16_03_total2, half_16_03_total3, half_16_03_total4, half_16_03_total5, half_16_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_03) (half_12_03)
    (by simpa only [half_16_03_φ6, show (2:ℝ)*32=64 by norm_num] using half_16_03_hx6)
  exact h.weaken (by norm_num [half_16_03_total1, half_16_03_total2, half_16_03_total3, half_16_03_total4, half_16_03_total5, half_16_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_03_hx4 : SourcePowerBound
    (powerBoxCross 9 12 16 half_16_03_φ4) (115537908497/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (38066573/500000000 : ℝ)) half_16_03_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_03_bounds4 l).1) (fun l => (half_16_03_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_03_total1, half_16_03_total2, half_16_03_total3, half_16_03_total4, half_16_03_total5, half_16_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_03) (half_13_03)
    (by simpa only [half_16_03_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_03_hx5)
  exact h.weaken (by norm_num [half_16_03_total1, half_16_03_total2, half_16_03_total3, half_16_03_total4, half_16_03_total5, half_16_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_03_hx3 : SourcePowerBound
    (powerBoxCross 9 13 8 half_16_03_φ3) (139368626061/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (870093097/10000000000 : ℝ)) half_16_03_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_03_bounds3 l).1) (fun l => (half_16_03_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_03_total1, half_16_03_total2, half_16_03_total3, half_16_03_total4, half_16_03_total5, half_16_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_03) (half_14_03)
    (by simpa only [half_16_03_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_03_hx4)
  exact h.weaken (by norm_num [half_16_03_total1, half_16_03_total2, half_16_03_total3, half_16_03_total4, half_16_03_total5, half_16_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_03_hx2 : SourcePowerBound
    (powerBoxCross 9 14 4 half_16_03_φ2) (169508266879/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (61326853/625000000 : ℝ)) half_16_03_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_03_bounds2 l).1) (fun l => (half_16_03_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_03_total1, half_16_03_total2, half_16_03_total3, half_16_03_total4, half_16_03_total5, half_16_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_03) (half_15_03)
    (by simpa only [half_16_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_03_hx3)
  exact h.weaken (by norm_num [half_16_03_total1, half_16_03_total2, half_16_03_total3, half_16_03_total4, half_16_03_total5, half_16_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_03_hx1 : SourcePowerBound
    (powerBoxCross 9 15 2 half_16_03_φ1) (51111423619/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (1009800141/10000000000 : ℝ)) half_16_03_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_03_bounds1 l).1) (fun l => (half_16_03_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_03_total1, half_16_03_total2, half_16_03_total3, half_16_03_total4, half_16_03_total5, half_16_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_03) (chord_64)
    (by simpa only [half_16_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_03_hx2)
  exact h.weaken (by norm_num [half_16_03_total1, half_16_03_total2, half_16_03_total3, half_16_03_total4, half_16_03_total5, half_16_03_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_16_03 : AdmissibleExponent 9 32 (23484423183/1000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 14) (ψ := (524112713/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_15_03)
    (by simpa only [half_16_03_φ1] using half_16_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_03_total1, half_16_03_total2, half_16_03_total3, half_16_03_total4, half_16_03_total5, half_16_03_total6, parameterExponent, curveLoss, dyadicExponent])

theorem chord_65 : AdmissibleExponent 9 34 (25417351379/1000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 34) (t := (1/2 : ℝ))
    (half_16_03) (half_18_02)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_17_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1062580039/10000000000 : ℝ)

private theorem half_17_03_total1 : total half_17_03_φ1=(1062580039/10000000000 : ℝ) := by
  norm_num [half_17_03_φ1,total,emptyPhi,Fin.snoc]

private theorem half_17_03_bounds1 : ∀ l,0≤half_17_03_φ1 l ∧ half_17_03_φ1 l≤1 ∧
    0≤shiftExponents 9 half_17_03_φ1 l :=
  alternate_bounds_snoc emptyPhi (1062580039/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_17_03_φ2 : Fin 2 → ℝ := Fin.snoc half_17_03_φ1 (1030757397/10000000000 : ℝ)

private theorem half_17_03_total2 : total half_17_03_φ2=(523334359/2500000000 : ℝ) := by
  change total (Fin.snoc half_17_03_φ1 (1030757397/10000000000 : ℝ))=(523334359/2500000000 : ℝ)
  rw [alternate_total_snoc,half_17_03_total1]
  norm_num

private theorem half_17_03_bounds2 : ∀ l,0≤half_17_03_φ2 l ∧ half_17_03_φ2 l≤1 ∧
    0≤shiftExponents 9 half_17_03_φ2 l :=
  alternate_bounds_snoc half_17_03_φ1 (1030757397/10000000000 : ℝ) half_17_03_bounds1 (by norm_num)

private def half_17_03_φ3 : Fin 3 → ℝ := Fin.snoc half_17_03_φ2 (49416641/500000000 : ℝ)

private theorem half_17_03_total3 : total half_17_03_φ3=(192604391/625000000 : ℝ) := by
  change total (Fin.snoc half_17_03_φ2 (49416641/500000000 : ℝ))=(192604391/625000000 : ℝ)
  rw [alternate_total_snoc,half_17_03_total2]
  norm_num

private theorem half_17_03_bounds3 : ∀ l,0≤half_17_03_φ3 l ∧ half_17_03_φ3 l≤1 ∧
    0≤shiftExponents 9 half_17_03_φ3 l :=
  alternate_bounds_snoc half_17_03_φ2 (49416641/500000000 : ℝ) half_17_03_bounds2 (by norm_num)

private def half_17_03_φ4 : Fin 4 → ℝ := Fin.snoc half_17_03_φ3 (864791217/10000000000 : ℝ)

private theorem half_17_03_total4 : total half_17_03_φ4=(3946461473/10000000000 : ℝ) := by
  change total (Fin.snoc half_17_03_φ3 (864791217/10000000000 : ℝ))=(3946461473/10000000000 : ℝ)
  rw [alternate_total_snoc,half_17_03_total3]
  norm_num

private theorem half_17_03_bounds4 : ∀ l,0≤half_17_03_φ4 l ∧ half_17_03_φ4 l≤1 ∧
    0≤shiftExponents 9 half_17_03_φ4 l :=
  alternate_bounds_snoc half_17_03_φ3 (864791217/10000000000 : ℝ) half_17_03_bounds3 (by norm_num)

private def half_17_03_φ5 : Fin 5 → ℝ := Fin.snoc half_17_03_φ4 (151338463/2000000000 : ℝ)

private theorem half_17_03_total5 : total half_17_03_φ5=(1175788447/2500000000 : ℝ) := by
  change total (Fin.snoc half_17_03_φ4 (151338463/2000000000 : ℝ))=(1175788447/2500000000 : ℝ)
  rw [alternate_total_snoc,half_17_03_total4]
  norm_num

private theorem half_17_03_bounds5 : ∀ l,0≤half_17_03_φ5 l ∧ half_17_03_φ5 l≤1 ∧
    0≤shiftExponents 9 half_17_03_φ5 l :=
  alternate_bounds_snoc half_17_03_φ4 (151338463/2000000000 : ℝ) half_17_03_bounds4 (by norm_num)

private def half_17_03_φ6 : Fin 6 → ℝ := Fin.snoc half_17_03_φ5 (41381611/625000000 : ℝ)

private theorem half_17_03_total6 : total half_17_03_φ6=(1341314891/2500000000 : ℝ) := by
  change total (Fin.snoc half_17_03_φ5 (41381611/625000000 : ℝ))=(1341314891/2500000000 : ℝ)
  rw [alternate_total_snoc,half_17_03_total5]
  norm_num

private theorem half_17_03_bounds6 : ∀ l,0≤half_17_03_φ6 l ∧ half_17_03_φ6 l≤1 ∧
    0≤shiftExponents 9 half_17_03_φ6 l :=
  alternate_bounds_snoc half_17_03_φ5 (41381611/625000000 : ℝ) half_17_03_bounds5 (by norm_num)

private theorem half_17_03_prefix : PrefixCondition 9 half_17_03_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_17_03_φ1, half_17_03_φ2, half_17_03_φ3, half_17_03_φ4, half_17_03_φ5, half_17_03_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_17_03_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_17_03_φ6) (2226055327/312500000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_17_03_φ6
    (fun i => (half_17_03_bounds6 i).1) (fun i => (half_17_03_bounds6 i).2.1)
    (fun i => (half_17_03_bounds6 i).2.2) half_17_03_prefix
  convert h using 1 <;> norm_num [half_17_03_total1, half_17_03_total2, half_17_03_total3, half_17_03_total4, half_17_03_total5, half_17_03_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_17_03_hx6 : SourcePowerBound
    (powerBoxCross 9 11 64 half_17_03_φ6) (45381109501/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 11) (r := 2) (v := 14) (w := 15) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_17_03_φ6 (by norm_num [half_17_03_total1, half_17_03_total2, half_17_03_total3, half_17_03_total4, half_17_03_total5, half_17_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_17_03_total1, half_17_03_total2, half_17_03_total3, half_17_03_total4, half_17_03_total5, half_17_03_total6, parameterExponent, curveLoss, dyadicExponent]) half_17_03_hF2
    (half_14_03) (half_15_03)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_03_total1, half_17_03_total2, half_17_03_total3, half_17_03_total4, half_17_03_total5, half_17_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_03_hx5 : SourcePowerBound
    (powerBoxCross 9 12 32 half_17_03_φ5) (53012061467/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 12) (u := 10) (t := 13)
    (D := 32) (ψ := (41381611/625000000 : ℝ)) half_17_03_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_03_bounds5 l).1) (fun l => (half_17_03_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_03_total1, half_17_03_total2, half_17_03_total3, half_17_03_total4, half_17_03_total5, half_17_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_03) (half_13_03)
    (by simpa only [half_17_03_φ6, show (2:ℝ)*32=64 by norm_num] using half_17_03_hx6)
  exact h.weaken (by norm_num [half_17_03_total1, half_17_03_total2, half_17_03_total3, half_17_03_total4, half_17_03_total5, half_17_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_03_hx4 : SourcePowerBound
    (powerBoxCross 9 13 16 half_17_03_φ4) (25143681661/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (151338463/2000000000 : ℝ)) half_17_03_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_03_bounds4 l).1) (fun l => (half_17_03_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_03_total1, half_17_03_total2, half_17_03_total3, half_17_03_total4, half_17_03_total5, half_17_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_03) (half_14_03)
    (by simpa only [half_17_03_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_03_hx5)
  exact h.weaken (by norm_num [half_17_03_total1, half_17_03_total2, half_17_03_total3, half_17_03_total4, half_17_03_total5, half_17_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_03_hx3 : SourcePowerBound
    (powerBoxCross 9 14 8 half_17_03_φ3) (151075498467/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (864791217/10000000000 : ℝ)) half_17_03_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_03_bounds3 l).1) (fun l => (half_17_03_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_03_total1, half_17_03_total2, half_17_03_total3, half_17_03_total4, half_17_03_total5, half_17_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_03) (half_15_03)
    (by simpa only [half_17_03_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_03_hx4)
  exact h.weaken (by norm_num [half_17_03_total1, half_17_03_total2, half_17_03_total3, half_17_03_total4, half_17_03_total5, half_17_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_03_hx2 : SourcePowerBound
    (powerBoxCross 9 15 4 half_17_03_φ2) (183348597369/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (49416641/500000000 : ℝ)) half_17_03_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_03_bounds2 l).1) (fun l => (half_17_03_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_03_total1, half_17_03_total2, half_17_03_total3, half_17_03_total4, half_17_03_total5, half_17_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_03) (half_16_03)
    (by simpa only [half_17_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_03_hx3)
  exact h.weaken (by norm_num [half_17_03_total1, half_17_03_total2, half_17_03_total3, half_17_03_total4, half_17_03_total5, half_17_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_03_hx1 : SourcePowerBound
    (powerBoxCross 9 16 2 half_17_03_φ1) (220952732571/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (1030757397/10000000000 : ℝ)) half_17_03_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_03_bounds1 l).1) (fun l => (half_17_03_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_03_total1, half_17_03_total2, half_17_03_total3, half_17_03_total4, half_17_03_total5, half_17_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_03) (chord_65)
    (by simpa only [half_17_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_03_hx2)
  exact h.weaken (by norm_num [half_17_03_total1, half_17_03_total2, half_17_03_total3, half_17_03_total4, half_17_03_total5, half_17_03_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_17_03 : AdmissibleExponent 9 34 (12694635689/500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 15) (ψ := (1062580039/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_16_03)
    (by simpa only [half_17_03_φ1] using half_17_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_03_total1, half_17_03_total2, half_17_03_total3, half_17_03_total4, half_17_03_total5, half_17_03_total6, parameterExponent, curveLoss, dyadicExponent])

theorem chord_66 : AdmissibleExponent 9 36 (273406939517/10000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 36) (t := (1/2 : ℝ))
    (half_17_03) (half_19_02)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_18_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (42980443/400000000 : ℝ)

private theorem half_18_03_total1 : total half_18_03_φ1=(42980443/400000000 : ℝ) := by
  norm_num [half_18_03_φ1,total,emptyPhi,Fin.snoc]

private theorem half_18_03_bounds1 : ∀ l,0≤half_18_03_φ1 l ∧ half_18_03_φ1 l≤1 ∧
    0≤shiftExponents 9 half_18_03_φ1 l :=
  alternate_bounds_snoc emptyPhi (42980443/400000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_18_03_φ2 : Fin 2 → ℝ := Fin.snoc half_18_03_φ1 (104813807/1000000000 : ℝ)

private theorem half_18_03_total2 : total half_18_03_φ2=(424529829/2000000000 : ℝ) := by
  change total (Fin.snoc half_18_03_φ1 (104813807/1000000000 : ℝ))=(424529829/2000000000 : ℝ)
  rw [alternate_total_snoc,half_18_03_total1]
  norm_num

private theorem half_18_03_bounds2 : ∀ l,0≤half_18_03_φ2 l ∧ half_18_03_φ2 l≤1 ∧
    0≤shiftExponents 9 half_18_03_φ2 l :=
  alternate_bounds_snoc half_18_03_φ1 (104813807/1000000000 : ℝ) half_18_03_bounds1 (by norm_num)

private def half_18_03_φ3 : Fin 3 → ℝ := Fin.snoc half_18_03_φ2 (123083607/1250000000 : ℝ)

private theorem half_18_03_total3 : total half_18_03_φ3=(3107318001/10000000000 : ℝ) := by
  change total (Fin.snoc half_18_03_φ2 (123083607/1250000000 : ℝ))=(3107318001/10000000000 : ℝ)
  rw [alternate_total_snoc,half_18_03_total2]
  norm_num

private theorem half_18_03_bounds3 : ∀ l,0≤half_18_03_φ3 l ∧ half_18_03_φ3 l≤1 ∧
    0≤shiftExponents 9 half_18_03_φ3 l :=
  alternate_bounds_snoc half_18_03_φ2 (123083607/1250000000 : ℝ) half_18_03_bounds2 (by norm_num)

private def half_18_03_φ4 : Fin 4 → ℝ := Fin.snoc half_18_03_φ3 (861585249/10000000000 : ℝ)

private theorem half_18_03_total4 : total half_18_03_φ4=(15875613/40000000 : ℝ) := by
  change total (Fin.snoc half_18_03_φ3 (861585249/10000000000 : ℝ))=(15875613/40000000 : ℝ)
  rw [alternate_total_snoc,half_18_03_total3]
  norm_num

private theorem half_18_03_bounds4 : ∀ l,0≤half_18_03_φ4 l ∧ half_18_03_φ4 l≤1 ∧
    0≤shiftExponents 9 half_18_03_φ4 l :=
  alternate_bounds_snoc half_18_03_φ3 (861585249/10000000000 : ℝ) half_18_03_bounds3 (by norm_num)

private def half_18_03_φ5 : Fin 5 → ℝ := Fin.snoc half_18_03_φ4 (753887093/10000000000 : ℝ)

private theorem half_18_03_total5 : total half_18_03_φ5=(4722790343/10000000000 : ℝ) := by
  change total (Fin.snoc half_18_03_φ4 (753887093/10000000000 : ℝ))=(4722790343/10000000000 : ℝ)
  rw [alternate_total_snoc,half_18_03_total4]
  norm_num

private theorem half_18_03_bounds5 : ∀ l,0≤half_18_03_φ5 l ∧ half_18_03_φ5 l≤1 ∧
    0≤shiftExponents 9 half_18_03_φ5 l :=
  alternate_bounds_snoc half_18_03_φ4 (753887093/10000000000 : ℝ) half_18_03_bounds4 (by norm_num)

private def half_18_03_φ6 : Fin 6 → ℝ := Fin.snoc half_18_03_φ5 (329825603/5000000000 : ℝ)

private theorem half_18_03_total6 : total half_18_03_φ6=(5382441549/10000000000 : ℝ) := by
  change total (Fin.snoc half_18_03_φ5 (329825603/5000000000 : ℝ))=(5382441549/10000000000 : ℝ)
  rw [alternate_total_snoc,half_18_03_total5]
  norm_num

private theorem half_18_03_bounds6 : ∀ l,0≤half_18_03_φ6 l ∧ half_18_03_φ6 l≤1 ∧
    0≤shiftExponents 9 half_18_03_φ6 l :=
  alternate_bounds_snoc half_18_03_φ5 (329825603/5000000000 : ℝ) half_18_03_bounds5 (by norm_num)

private theorem half_18_03_prefix : PrefixCondition 9 half_18_03_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_18_03_φ1, half_18_03_φ2, half_18_03_φ3, half_18_03_φ4, half_18_03_φ5, half_18_03_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_18_03_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_18_03_φ6) (8852675353/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_18_03_φ6
    (fun i => (half_18_03_bounds6 i).1) (fun i => (half_18_03_bounds6 i).2.1)
    (fun i => (half_18_03_bounds6 i).2.2) half_18_03_prefix
  convert h using 1 <;> norm_num [half_18_03_total1, half_18_03_total2, half_18_03_total3, half_18_03_total4, half_18_03_total5, half_18_03_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_18_03_hx6 : SourcePowerBound
    (powerBoxCross 9 12 64 half_18_03_φ6) (49517936629/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 12) (r := 2) (v := 0) (w := 16) (D := 64)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_18_03_φ6 (by norm_num [half_18_03_total1, half_18_03_total2, half_18_03_total3, half_18_03_total4, half_18_03_total5, half_18_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_18_03_total1, half_18_03_total2, half_18_03_total3, half_18_03_total4, half_18_03_total5, half_18_03_total6, parameterExponent, curveLoss, dyadicExponent]) half_18_03_hF2
    (admissibleExponent_zero 9) (half_16_03)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_18_03_total1, half_18_03_total2, half_18_03_total3, half_18_03_total4, half_18_03_total5, half_18_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_03_hx5 : SourcePowerBound
    (powerBoxCross 9 13 32 half_18_03_φ5) (23067053589/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 13) (u := 11) (t := 14)
    (D := 32) (ψ := (329825603/5000000000 : ℝ)) half_18_03_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_03_bounds5 l).1) (fun l => (half_18_03_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_03_total1, half_18_03_total2, half_18_03_total3, half_18_03_total4, half_18_03_total5, half_18_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_03) (half_14_03)
    (by simpa only [half_18_03_φ6, show (2:ℝ)*32=64 by norm_num] using half_18_03_hx6)
  exact h.weaken (by norm_num [half_18_03_total1, half_18_03_total2, half_18_03_total3, half_18_03_total4, half_18_03_total5, half_18_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_03_hx4 : SourcePowerBound
    (powerBoxCross 9 14 16 half_18_03_φ4) (852278993/62500000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 14) (u := 12) (t := 15)
    (D := 16) (ψ := (753887093/10000000000 : ℝ)) half_18_03_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_03_bounds4 l).1) (fun l => (half_18_03_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_03_total1, half_18_03_total2, half_18_03_total3, half_18_03_total4, half_18_03_total5, half_18_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_03) (half_15_03)
    (by simpa only [half_18_03_φ5, show (2:ℝ)*16=32 by norm_num] using half_18_03_hx5)
  exact h.weaken (by norm_num [half_18_03_total1, half_18_03_total2, half_18_03_total3, half_18_03_total4, half_18_03_total5, half_18_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_03_hx3 : SourcePowerBound
    (powerBoxCross 9 15 8 half_18_03_φ3) (163319778763/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 15) (u := 13) (t := 16)
    (D := 8) (ψ := (861585249/10000000000 : ℝ)) half_18_03_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_03_bounds3 l).1) (fun l => (half_18_03_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_03_total1, half_18_03_total2, half_18_03_total3, half_18_03_total4, half_18_03_total5, half_18_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_03) (half_16_03)
    (by simpa only [half_18_03_φ4, show (2:ℝ)*8=16 by norm_num] using half_18_03_hx4)
  exact h.weaken (by norm_num [half_18_03_total1, half_18_03_total2, half_18_03_total3, half_18_03_total4, half_18_03_total5, half_18_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_03_hx2 : SourcePowerBound
    (powerBoxCross 9 16 4 half_18_03_φ2) (197447090513/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 16) (u := 14) (t := 17)
    (D := 4) (ψ := (123083607/1250000000 : ℝ)) half_18_03_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_03_bounds2 l).1) (fun l => (half_18_03_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_03_total1, half_18_03_total2, half_18_03_total3, half_18_03_total4, half_18_03_total5, half_18_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_03) (half_17_03)
    (by simpa only [half_18_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_18_03_hx3)
  exact h.weaken (by norm_num [half_18_03_total1, half_18_03_total2, half_18_03_total3, half_18_03_total4, half_18_03_total5, half_18_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_03_hx1 : SourcePowerBound
    (powerBoxCross 9 17 2 half_18_03_φ1) (29710771447/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 17) (u := 15) (t := 18)
    (D := 2) (ψ := (104813807/1000000000 : ℝ)) half_18_03_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_03_bounds1 l).1) (fun l => (half_18_03_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_03_total1, half_18_03_total2, half_18_03_total3, half_18_03_total4, half_18_03_total5, half_18_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_03) (chord_66)
    (by simpa only [half_18_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_18_03_hx2)
  exact h.weaken (by norm_num [half_18_03_total1, half_18_03_total2, half_18_03_total3, half_18_03_total4, half_18_03_total5, half_18_03_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_18_03 : AdmissibleExponent 9 36 (273145037051/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 16) (ψ := (42980443/400000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_17_03)
    (by simpa only [half_18_03_φ1] using half_18_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_18_03_total1, half_18_03_total2, half_18_03_total3, half_18_03_total4, half_18_03_total5, half_18_03_total6, parameterExponent, curveLoss, dyadicExponent])

theorem chord_67 : AdmissibleExponent 9 38 (73206068883/2500000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 38) (t := (1/2 : ℝ))
    (half_18_03) (half_20_02)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_19_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (216967871/2000000000 : ℝ)

private theorem half_19_03_total1 : total half_19_03_φ1=(216967871/2000000000 : ℝ) := by
  norm_num [half_19_03_φ1,total,emptyPhi,Fin.snoc]

private theorem half_19_03_bounds1 : ∀ l,0≤half_19_03_φ1 l ∧ half_19_03_φ1 l≤1 ∧
    0≤shiftExponents 9 half_19_03_φ1 l :=
  alternate_bounds_snoc emptyPhi (216967871/2000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_19_03_φ2 : Fin 2 → ℝ := Fin.snoc half_19_03_φ1 (16597221/156250000 : ℝ)

private theorem half_19_03_total2 : total half_19_03_φ2=(2147061499/10000000000 : ℝ) := by
  change total (Fin.snoc half_19_03_φ1 (16597221/156250000 : ℝ))=(2147061499/10000000000 : ℝ)
  rw [alternate_total_snoc,half_19_03_total1]
  norm_num

private theorem half_19_03_bounds2 : ∀ l,0≤half_19_03_φ2 l ∧ half_19_03_φ2 l≤1 ∧
    0≤shiftExponents 9 half_19_03_φ2 l :=
  alternate_bounds_snoc half_19_03_φ1 (16597221/156250000 : ℝ) half_19_03_bounds1 (by norm_num)

private def half_19_03_φ3 : Fin 3 → ℝ := Fin.snoc half_19_03_φ2 (30675541/312500000 : ℝ)

private theorem half_19_03_total3 : total half_19_03_φ3=(3128678811/10000000000 : ℝ) := by
  change total (Fin.snoc half_19_03_φ2 (30675541/312500000 : ℝ))=(3128678811/10000000000 : ℝ)
  rw [alternate_total_snoc,half_19_03_total2]
  norm_num

private theorem half_19_03_bounds3 : ∀ l,0≤half_19_03_φ3 l ∧ half_19_03_φ3 l≤1 ∧
    0≤shiftExponents 9 half_19_03_φ3 l :=
  alternate_bounds_snoc half_19_03_φ2 (30675541/312500000 : ℝ) half_19_03_bounds2 (by norm_num)

private def half_19_03_φ4 : Fin 4 → ℝ := Fin.snoc half_19_03_φ3 (214728787/2500000000 : ℝ)

private theorem half_19_03_total4 : total half_19_03_φ4=(3987593959/10000000000 : ℝ) := by
  change total (Fin.snoc half_19_03_φ3 (214728787/2500000000 : ℝ))=(3987593959/10000000000 : ℝ)
  rw [alternate_total_snoc,half_19_03_total3]
  norm_num

private theorem half_19_03_bounds4 : ∀ l,0≤half_19_03_φ4 l ∧ half_19_03_φ4 l≤1 ∧
    0≤shiftExponents 9 half_19_03_φ4 l :=
  alternate_bounds_snoc half_19_03_φ3 (214728787/2500000000 : ℝ) half_19_03_bounds3 (by norm_num)

private def half_19_03_φ5 : Fin 5 → ℝ := Fin.snoc half_19_03_φ4 (375775377/5000000000 : ℝ)

private theorem half_19_03_total5 : total half_19_03_φ5=(4739144713/10000000000 : ℝ) := by
  change total (Fin.snoc half_19_03_φ4 (375775377/5000000000 : ℝ))=(4739144713/10000000000 : ℝ)
  rw [alternate_total_snoc,half_19_03_total4]
  norm_num

private theorem half_19_03_bounds5 : ∀ l,0≤half_19_03_φ5 l ∧ half_19_03_φ5 l≤1 ∧
    0≤shiftExponents 9 half_19_03_φ5 l :=
  alternate_bounds_snoc half_19_03_φ4 (375775377/5000000000 : ℝ) half_19_03_bounds4 (by norm_num)

private def half_19_03_φ6 : Fin 6 → ℝ := Fin.snoc half_19_03_φ5 (65760691/1000000000 : ℝ)

private theorem half_19_03_total6 : total half_19_03_φ6=(5396751623/10000000000 : ℝ) := by
  change total (Fin.snoc half_19_03_φ5 (65760691/1000000000 : ℝ))=(5396751623/10000000000 : ℝ)
  rw [alternate_total_snoc,half_19_03_total5]
  norm_num

private theorem half_19_03_bounds6 : ∀ l,0≤half_19_03_φ6 l ∧ half_19_03_φ6 l≤1 ∧
    0≤shiftExponents 9 half_19_03_φ6 l :=
  alternate_bounds_snoc half_19_03_φ5 (65760691/1000000000 : ℝ) half_19_03_bounds5 (by norm_num)

private theorem half_19_03_prefix : PrefixCondition 9 half_19_03_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_19_03_φ1, half_19_03_φ2, half_19_03_φ3, half_19_03_φ4, half_19_03_φ5, half_19_03_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_19_03_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_19_03_φ6) (8809745131/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_19_03_φ6
    (fun i => (half_19_03_bounds6 i).1) (fun i => (half_19_03_bounds6 i).2.1)
    (fun i => (half_19_03_bounds6 i).2.2) half_19_03_prefix
  convert h using 1 <;> norm_num [half_19_03_total1, half_19_03_total2, half_19_03_total3, half_19_03_total4, half_19_03_total5, half_19_03_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_19_03_hx6 : SourcePowerBound
    (powerBoxCross 9 13 64 half_19_03_φ6) (107489912607/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 13) (r := 2) (v := 17) (w := 18) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_19_03_φ6 (by norm_num [half_19_03_total1, half_19_03_total2, half_19_03_total3, half_19_03_total4, half_19_03_total5, half_19_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_19_03_total1, half_19_03_total2, half_19_03_total3, half_19_03_total4, half_19_03_total5, half_19_03_total6, parameterExponent, curveLoss, dyadicExponent]) half_19_03_hF2
    (half_17_03) (half_18_03)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_19_03_total1, half_19_03_total2, half_19_03_total3, half_19_03_total4, half_19_03_total5, half_19_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_03_hx5 : SourcePowerBound
    (powerBoxCross 9 14 32 half_19_03_φ5) (124837201477/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 14) (u := 12) (t := 15)
    (D := 32) (ψ := (65760691/1000000000 : ℝ)) half_19_03_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_03_bounds5 l).1) (fun l => (half_19_03_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_03_total1, half_19_03_total2, half_19_03_total3, half_19_03_total4, half_19_03_total5, half_19_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_03) (half_15_03)
    (by simpa only [half_19_03_φ6, show (2:ℝ)*32=64 by norm_num] using half_19_03_hx6)
  exact h.weaken (by norm_num [half_19_03_total1, half_19_03_total2, half_19_03_total3, half_19_03_total4, half_19_03_total5, half_19_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_03_hx4 : SourcePowerBound
    (powerBoxCross 9 15 16 half_19_03_φ4) (147213103989/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 15) (u := 13) (t := 16)
    (D := 16) (ψ := (375775377/5000000000 : ℝ)) half_19_03_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_03_bounds4 l).1) (fun l => (half_19_03_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_03_total1, half_19_03_total2, half_19_03_total3, half_19_03_total4, half_19_03_total5, half_19_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_03) (half_16_03)
    (by simpa only [half_19_03_φ5, show (2:ℝ)*16=32 by norm_num] using half_19_03_hx5)
  exact h.weaken (by norm_num [half_19_03_total1, half_19_03_total2, half_19_03_total3, half_19_03_total4, half_19_03_total5, half_19_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_03_hx3 : SourcePowerBound
    (powerBoxCross 9 16 8 half_19_03_φ3) (175775025593/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 16) (u := 14) (t := 17)
    (D := 8) (ψ := (214728787/2500000000 : ℝ)) half_19_03_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_03_bounds3 l).1) (fun l => (half_19_03_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_03_total1, half_19_03_total2, half_19_03_total3, half_19_03_total4, half_19_03_total5, half_19_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_03) (half_17_03)
    (by simpa only [half_19_03_φ4, show (2:ℝ)*8=16 by norm_num] using half_19_03_hx4)
  exact h.weaken (by norm_num [half_19_03_total1, half_19_03_total2, half_19_03_total3, half_19_03_total4, half_19_03_total5, half_19_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_03_hx2 : SourcePowerBound
    (powerBoxCross 9 17 4 half_19_03_φ2) (52940973507/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 17) (u := 15) (t := 18)
    (D := 4) (ψ := (30675541/312500000 : ℝ)) half_19_03_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_03_bounds2 l).1) (fun l => (half_19_03_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_03_total1, half_19_03_total2, half_19_03_total3, half_19_03_total4, half_19_03_total5, half_19_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_03) (half_18_03)
    (by simpa only [half_19_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_19_03_hx3)
  exact h.weaken (by norm_num [half_19_03_total1, half_19_03_total2, half_19_03_total3, half_19_03_total4, half_19_03_total5, half_19_03_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_03_hx1 : SourcePowerBound
    (powerBoxCross 9 18 2 half_19_03_φ1) (254598027827/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 18) (u := 16) (t := 19)
    (D := 2) (ψ := (16597221/156250000 : ℝ)) half_19_03_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_03_bounds1 l).1) (fun l => (half_19_03_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_03_total1, half_19_03_total2, half_19_03_total3, half_19_03_total4, half_19_03_total5, half_19_03_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_03) (chord_67)
    (by simpa only [half_19_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_19_03_hx2)
  exact h.weaken (by norm_num [half_19_03_total1, half_19_03_total2, half_19_03_total3, half_19_03_total4, half_19_03_total5, half_19_03_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_19_03 : AdmissibleExponent 9 38 (73141851313/2500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 17) (ψ := (216967871/2000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_18_03)
    (by simpa only [half_19_03_φ1] using half_19_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_19_03_total1, half_19_03_total2, half_19_03_total3, half_19_03_total4, half_19_03_total5, half_19_03_total6, parameterExponent, curveLoss, dyadicExponent])

theorem chord_68 : AdmissibleExponent 9 40 (312417987629/10000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 40) (t := (1/2 : ℝ))
    (half_19_03) (half_21_02)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

end Waring.SeedCompletionAlternate9Seeds
