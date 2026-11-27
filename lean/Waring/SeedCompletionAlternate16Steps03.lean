import Waring.SeedCompletionAlternate16Steps02

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionAlternate16Seeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges SeedCompletionDivisorPowerScales
open PolicyCompletionSharpResidualSource

private def half_29_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1/16 : ℝ)

private theorem half_29_01_total1 : total half_29_01_φ1=(1/16 : ℝ) := by
  norm_num [half_29_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_29_01_bounds1 : ∀ l,0≤half_29_01_φ1 l ∧ half_29_01_φ1 l≤1 ∧
    0≤shiftExponents 16 half_29_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (1/16 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_29_01_φ2 : Fin 2 → ℝ := Fin.snoc half_29_01_φ1 (286812279/5000000000 : ℝ)

private theorem half_29_01_total2 : total half_29_01_φ2=(599312279/5000000000 : ℝ) := by
  change total (Fin.snoc half_29_01_φ1 (286812279/5000000000 : ℝ))=(599312279/5000000000 : ℝ)
  rw [alternate_total_snoc,half_29_01_total1]
  norm_num

private theorem half_29_01_bounds2 : ∀ l,0≤half_29_01_φ2 l ∧ half_29_01_φ2 l≤1 ∧
    0≤shiftExponents 16 half_29_01_φ2 l :=
  alternate_bounds_snoc half_29_01_φ1 (286812279/5000000000 : ℝ) half_29_01_bounds1 (by norm_num)

private def half_29_01_φ3 : Fin 3 → ℝ := Fin.snoc half_29_01_φ2 (568997599/10000000000 : ℝ)

private theorem half_29_01_total3 : total half_29_01_φ3=(1767622157/10000000000 : ℝ) := by
  change total (Fin.snoc half_29_01_φ2 (568997599/10000000000 : ℝ))=(1767622157/10000000000 : ℝ)
  rw [alternate_total_snoc,half_29_01_total2]
  norm_num

private theorem half_29_01_bounds3 : ∀ l,0≤half_29_01_φ3 l ∧ half_29_01_φ3 l≤1 ∧
    0≤shiftExponents 16 half_29_01_φ3 l :=
  alternate_bounds_snoc half_29_01_φ2 (568997599/10000000000 : ℝ) half_29_01_bounds2 (by norm_num)

private def half_29_01_φ4 : Fin 4 → ℝ := Fin.snoc half_29_01_φ3 (548825189/10000000000 : ℝ)

private theorem half_29_01_total4 : total half_29_01_φ4=(1158223673/5000000000 : ℝ) := by
  change total (Fin.snoc half_29_01_φ3 (548825189/10000000000 : ℝ))=(1158223673/5000000000 : ℝ)
  rw [alternate_total_snoc,half_29_01_total3]
  norm_num

private theorem half_29_01_bounds4 : ∀ l,0≤half_29_01_φ4 l ∧ half_29_01_φ4 l≤1 ∧
    0≤shiftExponents 16 half_29_01_φ4 l :=
  alternate_bounds_snoc half_29_01_φ3 (548825189/10000000000 : ℝ) half_29_01_bounds3 (by norm_num)

private def half_29_01_φ5 : Fin 5 → ℝ := Fin.snoc half_29_01_φ4 (512236843/10000000000 : ℝ)

private theorem half_29_01_total5 : total half_29_01_φ5=(2828684189/10000000000 : ℝ) := by
  change total (Fin.snoc half_29_01_φ4 (512236843/10000000000 : ℝ))=(2828684189/10000000000 : ℝ)
  rw [alternate_total_snoc,half_29_01_total4]
  norm_num

private theorem half_29_01_bounds5 : ∀ l,0≤half_29_01_φ5 l ∧ half_29_01_φ5 l≤1 ∧
    0≤shiftExponents 16 half_29_01_φ5 l :=
  alternate_bounds_snoc half_29_01_φ4 (512236843/10000000000 : ℝ) half_29_01_bounds4 (by norm_num)

private def half_29_01_φ6 : Fin 6 → ℝ := Fin.snoc half_29_01_φ5 (11952193/250000000 : ℝ)

private theorem half_29_01_total6 : total half_29_01_φ6=(3306771909/10000000000 : ℝ) := by
  change total (Fin.snoc half_29_01_φ5 (11952193/250000000 : ℝ))=(3306771909/10000000000 : ℝ)
  rw [alternate_total_snoc,half_29_01_total5]
  norm_num

private theorem half_29_01_bounds6 : ∀ l,0≤half_29_01_φ6 l ∧ half_29_01_φ6 l≤1 ∧
    0≤shiftExponents 16 half_29_01_φ6 l :=
  alternate_bounds_snoc half_29_01_φ5 (11952193/250000000 : ℝ) half_29_01_bounds5 (by norm_num)

private def half_29_01_φ7 : Fin 7 → ℝ := Fin.snoc half_29_01_φ6 (89243041/2000000000 : ℝ)

private theorem half_29_01_total7 : total half_29_01_φ7=(1876493557/5000000000 : ℝ) := by
  change total (Fin.snoc half_29_01_φ6 (89243041/2000000000 : ℝ))=(1876493557/5000000000 : ℝ)
  rw [alternate_total_snoc,half_29_01_total6]
  norm_num

private theorem half_29_01_bounds7 : ∀ l,0≤half_29_01_φ7 l ∧ half_29_01_φ7 l≤1 ∧
    0≤shiftExponents 16 half_29_01_φ7 l :=
  alternate_bounds_snoc half_29_01_φ6 (89243041/2000000000 : ℝ) half_29_01_bounds6 (by norm_num)

private def half_29_01_φ8 : Fin 8 → ℝ := Fin.snoc half_29_01_φ7 (16658701/400000000 : ℝ)

private theorem half_29_01_total8 : total half_29_01_φ8=(4169454639/10000000000 : ℝ) := by
  change total (Fin.snoc half_29_01_φ7 (16658701/400000000 : ℝ))=(4169454639/10000000000 : ℝ)
  rw [alternate_total_snoc,half_29_01_total7]
  norm_num

private theorem half_29_01_bounds8 : ∀ l,0≤half_29_01_φ8 l ∧ half_29_01_φ8 l≤1 ∧
    0≤shiftExponents 16 half_29_01_φ8 l :=
  alternate_bounds_snoc half_29_01_φ7 (16658701/400000000 : ℝ) half_29_01_bounds7 (by norm_num)

private def half_29_01_φ9 : Fin 9 → ℝ := Fin.snoc half_29_01_φ8 (388703023/10000000000 : ℝ)

private theorem half_29_01_total9 : total half_29_01_φ9=(2279078831/5000000000 : ℝ) := by
  change total (Fin.snoc half_29_01_φ8 (388703023/10000000000 : ℝ))=(2279078831/5000000000 : ℝ)
  rw [alternate_total_snoc,half_29_01_total8]
  norm_num

private theorem half_29_01_bounds9 : ∀ l,0≤half_29_01_φ9 l ∧ half_29_01_φ9 l≤1 ∧
    0≤shiftExponents 16 half_29_01_φ9 l :=
  alternate_bounds_snoc half_29_01_φ8 (388703023/10000000000 : ℝ) half_29_01_bounds8 (by norm_num)

private def half_29_01_φ10 : Fin 10 → ℝ := Fin.snoc half_29_01_φ9 (22674343/625000000 : ℝ)

private theorem half_29_01_total10 : total half_29_01_φ10=(98418943/200000000 : ℝ) := by
  change total (Fin.snoc half_29_01_φ9 (22674343/625000000 : ℝ))=(98418943/200000000 : ℝ)
  rw [alternate_total_snoc,half_29_01_total9]
  norm_num

private theorem half_29_01_bounds10 : ∀ l,0≤half_29_01_φ10 l ∧ half_29_01_φ10 l≤1 ∧
    0≤shiftExponents 16 half_29_01_φ10 l :=
  alternate_bounds_snoc half_29_01_φ9 (22674343/625000000 : ℝ) half_29_01_bounds9 (by norm_num)

private def half_29_01_φ11 : Fin 11 → ℝ := Fin.snoc half_29_01_φ10 (169301761/5000000000 : ℝ)

private theorem half_29_01_total11 : total half_29_01_φ11=(328721917/625000000 : ℝ) := by
  change total (Fin.snoc half_29_01_φ10 (169301761/5000000000 : ℝ))=(328721917/625000000 : ℝ)
  rw [alternate_total_snoc,half_29_01_total10]
  norm_num

private theorem half_29_01_bounds11 : ∀ l,0≤half_29_01_φ11 l ∧ half_29_01_φ11 l≤1 ∧
    0≤shiftExponents 16 half_29_01_φ11 l :=
  alternate_bounds_snoc half_29_01_φ10 (169301761/5000000000 : ℝ) half_29_01_bounds10 (by norm_num)

private theorem half_29_01_prefix : PrefixCondition 16 half_29_01_φ11 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_29_01_φ1, half_29_01_φ2, half_29_01_φ3, half_29_01_φ4, half_29_01_φ5, half_29_01_φ6, half_29_01_φ7, half_29_01_φ8, half_29_01_φ9, half_29_01_φ10, half_29_01_φ11, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_29_01_hF4 : SourcePowerBound
    (paddedMoment 16 0 4 2048 half_29_01_φ11) (3346839743/125000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 16) (j := 11) (r := 0) (n := 2) (D := 2048)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_29_01_φ11
    (fun i => (half_29_01_bounds11 i).1) (fun i => (half_29_01_bounds11 i).2.1)
    (fun i => (half_29_01_bounds11 i).2.2) half_29_01_prefix
  convert h using 1 <;> norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, half_29_01_total9, half_29_01_total10, half_29_01_total11, parameterExponent, curveLoss, dyadicExponent]

private theorem half_29_01_hF2 : SourcePowerBound
    (paddedMoment 16 0 2 2048 half_29_01_φ11) (1416502747/125000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 16) (j := 11) (r := 0) (n := 1) (D := 2048)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_29_01_φ11
    (fun i => (half_29_01_bounds11 i).1) (fun i => (half_29_01_bounds11 i).2.1)
    (fun i => (half_29_01_bounds11 i).2.2) half_29_01_prefix
  convert h using 1 <;> norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, half_29_01_total9, half_29_01_total10, half_29_01_total11, parameterExponent, curveLoss, dyadicExponent]

private theorem half_29_01_hx11 : SourcePowerBound
    (powerBoxCross 16 18 2048 half_29_01_φ11) (149344817919/10000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 18) (r := 2) (v := 4) (t := 23) (D := 2048)
    (a := (17/92 : ℝ)) (b := (3/92 : ℝ)) (c := (18/23 : ℝ))
    (by norm_num) half_29_01_φ11 (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, half_29_01_total9, half_29_01_total10, half_29_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, half_29_01_total9, half_29_01_total10, half_29_01_total11, parameterExponent, curveLoss, dyadicExponent]) half_29_01_hF2 half_29_01_hF4
    (half_23_01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, half_29_01_total9, half_29_01_total10, half_29_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_29_01_hx10 : SourcePowerBound
    (powerBoxCross 16 19 1024 half_29_01_φ10) (81094748151/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 10) (s := 19) (u := 17) (t := 20)
    (D := 1024) (ψ := (169301761/5000000000 : ℝ)) half_29_01_φ10
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_29_01_bounds10 l).1) (fun l => (half_29_01_bounds10 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, half_29_01_total9, half_29_01_total10, half_29_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_01) (half_20_01)
    (by simpa only [half_29_01_φ11, show (2:ℝ)*1024=2048 by norm_num] using half_29_01_hx11)
  exact h.weaken (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, half_29_01_total9, half_29_01_total10, half_29_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_29_01_hx9 : SourcePowerBound
    (powerBoxCross 16 20 512 half_29_01_φ9) (88372515969/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 9) (s := 20) (u := 18) (t := 21)
    (D := 512) (ψ := (22674343/625000000 : ℝ)) half_29_01_φ9
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_29_01_bounds9 l).1) (fun l => (half_29_01_bounds9 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, half_29_01_total9, half_29_01_total10, half_29_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_19_01) (half_21_01)
    (by simpa only [half_29_01_φ10, show (2:ℝ)*512=1024 by norm_num] using half_29_01_hx10)
  exact h.weaken (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, half_29_01_total9, half_29_01_total10, half_29_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_29_01_hx8 : SourcePowerBound
    (powerBoxCross 16 21 256 half_29_01_φ8) (193522681579/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 8) (s := 21) (u := 19) (t := 22)
    (D := 256) (ψ := (388703023/10000000000 : ℝ)) half_29_01_φ8
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_29_01_bounds8 l).1) (fun l => (half_29_01_bounds8 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, half_29_01_total9, half_29_01_total10, half_29_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_20_01) (half_22_01)
    (by simpa only [half_29_01_φ9, show (2:ℝ)*256=512 by norm_num] using half_29_01_hx9)
  exact h.weaken (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, half_29_01_total9, half_29_01_total10, half_29_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_29_01_hx7 : SourcePowerBound
    (powerBoxCross 16 22 128 half_29_01_φ7) (53227361839/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 7) (s := 22) (u := 20) (t := 23)
    (D := 128) (ψ := (16658701/400000000 : ℝ)) half_29_01_φ7
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_29_01_bounds7 l).1) (fun l => (half_29_01_bounds7 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, half_29_01_total9, half_29_01_total10, half_29_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_21_01) (half_23_01)
    (by simpa only [half_29_01_φ8, show (2:ℝ)*128=256 by norm_num] using half_29_01_hx8)
  exact h.weaken (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, half_29_01_total9, half_29_01_total10, half_29_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_29_01_hx6 : SourcePowerBound
    (powerBoxCross 16 23 64 half_29_01_φ6) (23524193543/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 6) (s := 23) (u := 21) (t := 24)
    (D := 64) (ψ := (89243041/2000000000 : ℝ)) half_29_01_φ6
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_29_01_bounds6 l).1) (fun l => (half_29_01_bounds6 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, half_29_01_total9, half_29_01_total10, half_29_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_22_01) (half_24_01)
    (by simpa only [half_29_01_φ7, show (2:ℝ)*64=128 by norm_num] using half_29_01_hx7)
  exact h.weaken (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, half_29_01_total9, half_29_01_total10, half_29_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_29_01_hx5 : SourcePowerBound
    (powerBoxCross 16 24 32 half_29_01_φ5) (26084617351/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 5) (s := 24) (u := 22) (t := 25)
    (D := 32) (ψ := (11952193/250000000 : ℝ)) half_29_01_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_29_01_bounds5 l).1) (fun l => (half_29_01_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, half_29_01_total9, half_29_01_total10, half_29_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_23_01) (half_25_01)
    (by simpa only [half_29_01_φ6, show (2:ℝ)*32=64 by norm_num] using half_29_01_hx6)
  exact h.weaken (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, half_29_01_total9, half_29_01_total10, half_29_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_29_01_hx4 : SourcePowerBound
    (powerBoxCross 16 25 16 half_29_01_φ4) (1133042189/39062500 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 25) (u := 23) (t := 26)
    (D := 16) (ψ := (512236843/10000000000 : ℝ)) half_29_01_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_29_01_bounds4 l).1) (fun l => (half_29_01_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, half_29_01_total9, half_29_01_total10, half_29_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_24_01) (half_26_01)
    (by simpa only [half_29_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_29_01_hx5)
  exact h.weaken (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, half_29_01_total9, half_29_01_total10, half_29_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_29_01_hx3 : SourcePowerBound
    (powerBoxCross 16 26 8 half_29_01_φ3) (323242849747/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 26) (u := 24) (t := 27)
    (D := 8) (ψ := (548825189/10000000000 : ℝ)) half_29_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_29_01_bounds3 l).1) (fun l => (half_29_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, half_29_01_total9, half_29_01_total10, half_29_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_25_01) (half_27_01)
    (by simpa only [half_29_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_29_01_hx4)
  exact h.weaken (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, half_29_01_total9, half_29_01_total10, half_29_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_29_01_hx2 : SourcePowerBound
    (powerBoxCross 16 27 4 half_29_01_φ2) (71956589989/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 27) (u := 25) (t := 28)
    (D := 4) (ψ := (568997599/10000000000 : ℝ)) half_29_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_29_01_bounds2 l).1) (fun l => (half_29_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, half_29_01_total9, half_29_01_total10, half_29_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_26_01) (half_28_01)
    (by simpa only [half_29_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_29_01_hx3)
  exact h.weaken (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, half_29_01_total9, half_29_01_total10, half_29_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_29_01_hx1 : SourcePowerBound
    (powerBoxCross 16 28 2 half_29_01_φ1) (400051074099/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 28) (u := 26) (t := 29)
    (D := 2) (ψ := (286812279/5000000000 : ℝ)) half_29_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_29_01_bounds1 l).1) (fun l => (half_29_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, half_29_01_total9, half_29_01_total10, half_29_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_27_01) (chord_73)
    (by simpa only [half_29_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_29_01_hx2)
  exact h.weaken (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, half_29_01_total9, half_29_01_total10, half_29_01_total11, parameterExponent, curveLoss, dyadicExponent])

theorem half_29_01 : AdmissibleExponent 16 58 (434426074099/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 27) (ψ := (1/16 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_28_01)
    (by simpa only [half_29_01_φ1] using half_29_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_29_01_total1, half_29_01_total2, half_29_01_total3, half_29_01_total4, half_29_01_total5, half_29_01_total6, half_29_01_total7, half_29_01_total8, half_29_01_total9, half_29_01_total10, half_29_01_total11, parameterExponent, curveLoss, dyadicExponent])

private def half_30_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1/16 : ℝ)

private theorem half_30_01_total1 : total half_30_01_φ1=(1/16 : ℝ) := by
  norm_num [half_30_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_30_01_bounds1 : ∀ l,0≤half_30_01_φ1 l ∧ half_30_01_φ1 l≤1 ∧
    0≤shiftExponents 16 half_30_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (1/16 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_30_01_φ2 : Fin 2 → ℝ := Fin.snoc half_30_01_φ1 (291598563/5000000000 : ℝ)

private theorem half_30_01_total2 : total half_30_01_φ2=(604098563/5000000000 : ℝ) := by
  change total (Fin.snoc half_30_01_φ1 (291598563/5000000000 : ℝ))=(604098563/5000000000 : ℝ)
  rw [alternate_total_snoc,half_30_01_total1]
  norm_num

private theorem half_30_01_bounds2 : ∀ l,0≤half_30_01_φ2 l ∧ half_30_01_φ2 l≤1 ∧
    0≤shiftExponents 16 half_30_01_φ2 l :=
  alternate_bounds_snoc half_30_01_φ1 (291598563/5000000000 : ℝ) half_30_01_bounds1 (by norm_num)

private def half_30_01_φ3 : Fin 3 → ℝ := Fin.snoc half_30_01_φ2 (35998411/625000000 : ℝ)

private theorem half_30_01_total3 : total half_30_01_φ3=(892085851/5000000000 : ℝ) := by
  change total (Fin.snoc half_30_01_φ2 (35998411/625000000 : ℝ))=(892085851/5000000000 : ℝ)
  rw [alternate_total_snoc,half_30_01_total2]
  norm_num

private theorem half_30_01_bounds3 : ∀ l,0≤half_30_01_φ3 l ∧ half_30_01_φ3 l≤1 ∧
    0≤shiftExponents 16 half_30_01_φ3 l :=
  alternate_bounds_snoc half_30_01_φ2 (35998411/625000000 : ℝ) half_30_01_bounds2 (by norm_num)

private def half_30_01_φ4 : Fin 4 → ℝ := Fin.snoc half_30_01_φ3 (273860943/5000000000 : ℝ)

private theorem half_30_01_total4 : total half_30_01_φ4=(582973397/2500000000 : ℝ) := by
  change total (Fin.snoc half_30_01_φ3 (273860943/5000000000 : ℝ))=(582973397/2500000000 : ℝ)
  rw [alternate_total_snoc,half_30_01_total3]
  norm_num

private theorem half_30_01_bounds4 : ∀ l,0≤half_30_01_φ4 l ∧ half_30_01_φ4 l≤1 ∧
    0≤shiftExponents 16 half_30_01_φ4 l :=
  alternate_bounds_snoc half_30_01_φ3 (273860943/5000000000 : ℝ) half_30_01_bounds3 (by norm_num)

private def half_30_01_φ5 : Fin 5 → ℝ := Fin.snoc half_30_01_φ4 (255603547/5000000000 : ℝ)

private theorem half_30_01_total5 : total half_30_01_φ5=(1421550341/5000000000 : ℝ) := by
  change total (Fin.snoc half_30_01_φ4 (255603547/5000000000 : ℝ))=(1421550341/5000000000 : ℝ)
  rw [alternate_total_snoc,half_30_01_total4]
  norm_num

private theorem half_30_01_bounds5 : ∀ l,0≤half_30_01_φ5 l ∧ half_30_01_φ5 l≤1 ∧
    0≤shiftExponents 16 half_30_01_φ5 l :=
  alternate_bounds_snoc half_30_01_φ4 (255603547/5000000000 : ℝ) half_30_01_bounds4 (by norm_num)

private def half_30_01_φ6 : Fin 6 → ℝ := Fin.snoc half_30_01_φ5 (477126621/10000000000 : ℝ)

private theorem half_30_01_total6 : total half_30_01_φ6=(3320227303/10000000000 : ℝ) := by
  change total (Fin.snoc half_30_01_φ5 (477126621/10000000000 : ℝ))=(3320227303/10000000000 : ℝ)
  rw [alternate_total_snoc,half_30_01_total5]
  norm_num

private theorem half_30_01_bounds6 : ∀ l,0≤half_30_01_φ6 l ∧ half_30_01_φ6 l≤1 ∧
    0≤shiftExponents 16 half_30_01_φ6 l :=
  alternate_bounds_snoc half_30_01_φ5 (477126621/10000000000 : ℝ) half_30_01_bounds5 (by norm_num)

private def half_30_01_φ7 : Fin 7 → ℝ := Fin.snoc half_30_01_φ6 (445318179/10000000000 : ℝ)

private theorem half_30_01_total7 : total half_30_01_φ7=(1882772741/5000000000 : ℝ) := by
  change total (Fin.snoc half_30_01_φ6 (445318179/10000000000 : ℝ))=(1882772741/5000000000 : ℝ)
  rw [alternate_total_snoc,half_30_01_total6]
  norm_num

private theorem half_30_01_bounds7 : ∀ l,0≤half_30_01_φ7 l ∧ half_30_01_φ7 l≤1 ∧
    0≤shiftExponents 16 half_30_01_φ7 l :=
  alternate_bounds_snoc half_30_01_φ6 (445318179/10000000000 : ℝ) half_30_01_bounds6 (by norm_num)

private def half_30_01_φ8 : Fin 8 → ℝ := Fin.snoc half_30_01_φ7 (415630301/10000000000 : ℝ)

private theorem half_30_01_total8 : total half_30_01_φ8=(4181175783/10000000000 : ℝ) := by
  change total (Fin.snoc half_30_01_φ7 (415630301/10000000000 : ℝ))=(4181175783/10000000000 : ℝ)
  rw [alternate_total_snoc,half_30_01_total7]
  norm_num

private theorem half_30_01_bounds8 : ∀ l,0≤half_30_01_φ8 l ∧ half_30_01_φ8 l≤1 ∧
    0≤shiftExponents 16 half_30_01_φ8 l :=
  alternate_bounds_snoc half_30_01_φ7 (415630301/10000000000 : ℝ) half_30_01_bounds7 (by norm_num)

private def half_30_01_φ9 : Fin 9 → ℝ := Fin.snoc half_30_01_φ8 (193960807/5000000000 : ℝ)

private theorem half_30_01_total9 : total half_30_01_φ9=(4569097397/10000000000 : ℝ) := by
  change total (Fin.snoc half_30_01_φ8 (193960807/5000000000 : ℝ))=(4569097397/10000000000 : ℝ)
  rw [alternate_total_snoc,half_30_01_total8]
  norm_num

private theorem half_30_01_bounds9 : ∀ l,0≤half_30_01_φ9 l ∧ half_30_01_φ9 l≤1 ∧
    0≤shiftExponents 16 half_30_01_φ9 l :=
  alternate_bounds_snoc half_30_01_φ8 (193960807/5000000000 : ℝ) half_30_01_bounds8 (by norm_num)

private def half_30_01_φ10 : Fin 10 → ℝ := Fin.snoc half_30_01_φ9 (362060173/10000000000 : ℝ)

private theorem half_30_01_total10 : total half_30_01_φ10=(493115757/1000000000 : ℝ) := by
  change total (Fin.snoc half_30_01_φ9 (362060173/10000000000 : ℝ))=(493115757/1000000000 : ℝ)
  rw [alternate_total_snoc,half_30_01_total9]
  norm_num

private theorem half_30_01_bounds10 : ∀ l,0≤half_30_01_φ10 l ∧ half_30_01_φ10 l≤1 ∧
    0≤shiftExponents 16 half_30_01_φ10 l :=
  alternate_bounds_snoc half_30_01_φ9 (362060173/10000000000 : ℝ) half_30_01_bounds9 (by norm_num)

private def half_30_01_φ11 : Fin 11 → ℝ := Fin.snoc half_30_01_φ10 (84480707/2500000000 : ℝ)

private theorem half_30_01_total11 : total half_30_01_φ11=(2634540199/5000000000 : ℝ) := by
  change total (Fin.snoc half_30_01_φ10 (84480707/2500000000 : ℝ))=(2634540199/5000000000 : ℝ)
  rw [alternate_total_snoc,half_30_01_total10]
  norm_num

private theorem half_30_01_bounds11 : ∀ l,0≤half_30_01_φ11 l ∧ half_30_01_φ11 l≤1 ∧
    0≤shiftExponents 16 half_30_01_φ11 l :=
  alternate_bounds_snoc half_30_01_φ10 (84480707/2500000000 : ℝ) half_30_01_bounds10 (by norm_num)

private theorem half_30_01_prefix : PrefixCondition 16 half_30_01_φ11 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_30_01_φ1, half_30_01_φ2, half_30_01_φ3, half_30_01_φ4, half_30_01_φ5, half_30_01_φ6, half_30_01_φ7, half_30_01_φ8, half_30_01_φ9, half_30_01_φ10, half_30_01_φ11, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_30_01_hF4 : SourcePowerBound
    (paddedMoment 16 0 4 2048 half_30_01_φ11) (26674655821/1000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 16) (j := 11) (r := 0) (n := 2) (D := 2048)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_30_01_φ11
    (fun i => (half_30_01_bounds11 i).1) (fun i => (half_30_01_bounds11 i).2.1)
    (fun i => (half_30_01_bounds11 i).2.2) half_30_01_prefix
  convert h using 1 <;> norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, half_30_01_total9, half_30_01_total10, half_30_01_total11, parameterExponent, curveLoss, dyadicExponent]

private theorem half_30_01_hF2 : SourcePowerBound
    (paddedMoment 16 0 2 2048 half_30_01_φ11) (11289138209/1000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 16) (j := 11) (r := 0) (n := 1) (D := 2048)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_30_01_φ11
    (fun i => (half_30_01_bounds11 i).1) (fun i => (half_30_01_bounds11 i).2.1)
    (fun i => (half_30_01_bounds11 i).2.2) half_30_01_prefix
  convert h using 1 <;> norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, half_30_01_total9, half_30_01_total10, half_30_01_total11, parameterExponent, curveLoss, dyadicExponent]

private theorem half_30_01_hx11 : SourcePowerBound
    (powerBoxCross 16 19 2048 half_30_01_φ11) (78704304229/5000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 19) (r := 2) (v := 4) (t := 23) (D := 2048)
    (a := (9/92 : ℝ)) (b := (7/92 : ℝ)) (c := (19/23 : ℝ))
    (by norm_num) half_30_01_φ11 (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, half_30_01_total9, half_30_01_total10, half_30_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, half_30_01_total9, half_30_01_total10, half_30_01_total11, parameterExponent, curveLoss, dyadicExponent]) half_30_01_hF2 half_30_01_hF4
    (half_23_01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, half_30_01_total9, half_30_01_total10, half_30_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_30_01_hx10 : SourcePowerBound
    (powerBoxCross 16 20 1024 half_30_01_φ10) (3414842947/200000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 10) (s := 20) (u := 18) (t := 21)
    (D := 1024) (ψ := (84480707/2500000000 : ℝ)) half_30_01_φ10
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_30_01_bounds10 l).1) (fun l => (half_30_01_bounds10 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, half_30_01_total9, half_30_01_total10, half_30_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_19_01) (half_21_01)
    (by simpa only [half_30_01_φ11, show (2:ℝ)*1024=2048 by norm_num] using half_30_01_hx11)
  exact h.weaken (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, half_30_01_total9, half_30_01_total10, half_30_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_30_01_hx9 : SourcePowerBound
    (powerBoxCross 16 21 512 half_30_01_φ9) (23239366751/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 9) (s := 21) (u := 19) (t := 22)
    (D := 512) (ψ := (362060173/10000000000 : ℝ)) half_30_01_φ9
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_30_01_bounds9 l).1) (fun l => (half_30_01_bounds9 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, half_30_01_total9, half_30_01_total10, half_30_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_20_01) (half_22_01)
    (by simpa only [half_30_01_φ10, show (2:ℝ)*512=1024 by norm_num] using half_30_01_hx10)
  exact h.weaken (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, half_30_01_total9, half_30_01_total10, half_30_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_30_01_hx8 : SourcePowerBound
    (powerBoxCross 16 22 256 half_30_01_φ8) (101701361143/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 8) (s := 22) (u := 20) (t := 23)
    (D := 256) (ψ := (193960807/5000000000 : ℝ)) half_30_01_φ8
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_30_01_bounds8 l).1) (fun l => (half_30_01_bounds8 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, half_30_01_total9, half_30_01_total10, half_30_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_21_01) (half_23_01)
    (by simpa only [half_30_01_φ9, show (2:ℝ)*256=512 by norm_num] using half_30_01_hx9)
  exact h.weaken (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, half_30_01_total9, half_30_01_total10, half_30_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_30_01_hx7 : SourcePowerBound
    (powerBoxCross 16 23 128 half_30_01_φ7) (44715337081/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 7) (s := 23) (u := 21) (t := 24)
    (D := 128) (ψ := (415630301/10000000000 : ℝ)) half_30_01_φ7
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_30_01_bounds7 l).1) (fun l => (half_30_01_bounds7 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, half_30_01_total9, half_30_01_total10, half_30_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_22_01) (half_24_01)
    (by simpa only [half_30_01_φ8, show (2:ℝ)*128=256 by norm_num] using half_30_01_hx8)
  exact h.weaken (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, half_30_01_total9, half_30_01_total10, half_30_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_30_01_hx6 : SourcePowerBound
    (powerBoxCross 16 24 64 half_30_01_φ6) (61692330901/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 6) (s := 24) (u := 22) (t := 25)
    (D := 64) (ψ := (445318179/10000000000 : ℝ)) half_30_01_φ6
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_30_01_bounds6 l).1) (fun l => (half_30_01_bounds6 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, half_30_01_total9, half_30_01_total10, half_30_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_23_01) (half_25_01)
    (by simpa only [half_30_01_φ7, show (2:ℝ)*64=128 by norm_num] using half_30_01_hx7)
  exact h.weaken (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, half_30_01_total9, half_30_01_total10, half_30_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_30_01_hx5 : SourcePowerBound
    (powerBoxCross 16 25 32 half_30_01_φ5) (273308611273/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 5) (s := 25) (u := 23) (t := 26)
    (D := 32) (ψ := (477126621/10000000000 : ℝ)) half_30_01_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_30_01_bounds5 l).1) (fun l => (half_30_01_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, half_30_01_total9, half_30_01_total10, half_30_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_24_01) (half_26_01)
    (by simpa only [half_30_01_φ6, show (2:ℝ)*32=64 by norm_num] using half_30_01_hx6)
  exact h.weaken (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, half_30_01_total9, half_30_01_total10, half_30_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_30_01_hx4 : SourcePowerBound
    (powerBoxCross 16 26 16 half_30_01_φ4) (303539903561/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 26) (u := 24) (t := 27)
    (D := 16) (ψ := (255603547/5000000000 : ℝ)) half_30_01_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_30_01_bounds4 l).1) (fun l => (half_30_01_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, half_30_01_total9, half_30_01_total10, half_30_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_25_01) (half_27_01)
    (by simpa only [half_30_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_30_01_hx5)
  exact h.weaken (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, half_30_01_total9, half_30_01_total10, half_30_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_30_01_hx3 : SourcePowerBound
    (powerBoxCross 16 27 8 half_30_01_φ3) (337846359169/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 27) (u := 25) (t := 28)
    (D := 8) (ψ := (273860943/5000000000 : ℝ)) half_30_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_30_01_bounds3 l).1) (fun l => (half_30_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, half_30_01_total9, half_30_01_total10, half_30_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_26_01) (half_28_01)
    (by simpa only [half_30_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_30_01_hx4)
  exact h.weaken (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, half_30_01_total9, half_30_01_total10, half_30_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_30_01_hx2 : SourcePowerBound
    (powerBoxCross 16 28 4 half_30_01_φ2) (2938237873/78125000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 28) (u := 26) (t := 29)
    (D := 4) (ψ := (35998411/625000000 : ℝ)) half_30_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_30_01_bounds2 l).1) (fun l => (half_30_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, half_30_01_total9, half_30_01_total10, half_30_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_27_01) (half_29_01)
    (by simpa only [half_30_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_30_01_hx3)
  exact h.weaken (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, half_30_01_total9, half_30_01_total10, half_30_01_total11, parameterExponent, curveLoss, dyadicExponent])

private theorem half_30_01_hx1 : SourcePowerBound
    (powerBoxCross 16 29 2 half_30_01_φ1) (209572199597/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 29) (u := 27) (t := 30)
    (D := 2) (ψ := (291598563/5000000000 : ℝ)) half_30_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_30_01_bounds1 l).1) (fun l => (half_30_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, half_30_01_total9, half_30_01_total10, half_30_01_total11, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_28_01) (half_30_00)
    (by simpa only [half_30_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_30_01_hx2)
  exact h.weaken (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, half_30_01_total9, half_30_01_total10, half_30_01_total11, parameterExponent, curveLoss, dyadicExponent])

theorem half_30_01 : AdmissibleExponent 16 60 (227384699597/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 28) (ψ := (1/16 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_29_01)
    (by simpa only [half_30_01_φ1] using half_30_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_30_01_total1, half_30_01_total2, half_30_01_total3, half_30_01_total4, half_30_01_total5, half_30_01_total6, half_30_01_total7, half_30_01_total8, half_30_01_total9, half_30_01_total10, half_30_01_total11, parameterExponent, curveLoss, dyadicExponent])

private def half_15_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (97720331/2000000000 : ℝ)

private theorem half_15_02_total1 : total half_15_02_φ1=(97720331/2000000000 : ℝ) := by
  norm_num [half_15_02_φ1,total,emptyPhi,Fin.snoc]

private theorem half_15_02_bounds1 : ∀ l,0≤half_15_02_φ1 l ∧ half_15_02_φ1 l≤1 ∧
    0≤shiftExponents 16 half_15_02_φ1 l :=
  alternate_bounds_snoc emptyPhi (97720331/2000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_15_02_φ2 : Fin 2 → ℝ := Fin.snoc half_15_02_φ1 (459517679/10000000000 : ℝ)

private theorem half_15_02_total2 : total half_15_02_φ2=(474059667/5000000000 : ℝ) := by
  change total (Fin.snoc half_15_02_φ1 (459517679/10000000000 : ℝ))=(474059667/5000000000 : ℝ)
  rw [alternate_total_snoc,half_15_02_total1]
  norm_num

private theorem half_15_02_bounds2 : ∀ l,0≤half_15_02_φ2 l ∧ half_15_02_φ2 l≤1 ∧
    0≤shiftExponents 16 half_15_02_φ2 l :=
  alternate_bounds_snoc half_15_02_φ1 (459517679/10000000000 : ℝ) half_15_02_bounds1 (by norm_num)

private def half_15_02_φ3 : Fin 3 → ℝ := Fin.snoc half_15_02_φ2 (444546383/10000000000 : ℝ)

private theorem half_15_02_total3 : total half_15_02_φ3=(1392665717/10000000000 : ℝ) := by
  change total (Fin.snoc half_15_02_φ2 (444546383/10000000000 : ℝ))=(1392665717/10000000000 : ℝ)
  rw [alternate_total_snoc,half_15_02_total2]
  norm_num

private theorem half_15_02_bounds3 : ∀ l,0≤half_15_02_φ3 l ∧ half_15_02_φ3 l≤1 ∧
    0≤shiftExponents 16 half_15_02_φ3 l :=
  alternate_bounds_snoc half_15_02_φ2 (444546383/10000000000 : ℝ) half_15_02_bounds2 (by norm_num)

private def half_15_02_φ4 : Fin 4 → ℝ := Fin.snoc half_15_02_φ3 (421601477/10000000000 : ℝ)

private theorem half_15_02_total4 : total half_15_02_φ4=(907133597/5000000000 : ℝ) := by
  change total (Fin.snoc half_15_02_φ3 (421601477/10000000000 : ℝ))=(907133597/5000000000 : ℝ)
  rw [alternate_total_snoc,half_15_02_total3]
  norm_num

private theorem half_15_02_bounds4 : ∀ l,0≤half_15_02_φ4 l ∧ half_15_02_φ4 l≤1 ∧
    0≤shiftExponents 16 half_15_02_φ4 l :=
  alternate_bounds_snoc half_15_02_φ3 (421601477/10000000000 : ℝ) half_15_02_bounds3 (by norm_num)

private def half_15_02_φ5 : Fin 5 → ℝ := Fin.snoc half_15_02_φ4 (23127823/625000000 : ℝ)

private theorem half_15_02_total5 : total half_15_02_φ5=(1092156181/5000000000 : ℝ) := by
  change total (Fin.snoc half_15_02_φ4 (23127823/625000000 : ℝ))=(1092156181/5000000000 : ℝ)
  rw [alternate_total_snoc,half_15_02_total4]
  norm_num

private theorem half_15_02_bounds5 : ∀ l,0≤half_15_02_φ5 l ∧ half_15_02_φ5 l≤1 ∧
    0≤shiftExponents 16 half_15_02_φ5 l :=
  alternate_bounds_snoc half_15_02_φ4 (23127823/625000000 : ℝ) half_15_02_bounds4 (by norm_num)

private def half_15_02_φ6 : Fin 6 → ℝ := Fin.snoc half_15_02_φ5 (96395957/5000000000 : ℝ)

private theorem half_15_02_total6 : total half_15_02_φ6=(594276069/2500000000 : ℝ) := by
  change total (Fin.snoc half_15_02_φ5 (96395957/5000000000 : ℝ))=(594276069/2500000000 : ℝ)
  rw [alternate_total_snoc,half_15_02_total5]
  norm_num

private theorem half_15_02_bounds6 : ∀ l,0≤half_15_02_φ6 l ∧ half_15_02_φ6 l≤1 ∧
    0≤shiftExponents 16 half_15_02_φ6 l :=
  alternate_bounds_snoc half_15_02_φ5 (96395957/5000000000 : ℝ) half_15_02_bounds5 (by norm_num)

private theorem half_15_02_prefix : PrefixCondition 16 half_15_02_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, half_15_02_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_15_02_hF2 : SourcePowerBound
    (paddedMoment 16 0 2 64 half_15_02_φ6) (4651515379/500000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 16) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_15_02_φ6
    (fun i => (half_15_02_bounds6 i).1) (fun i => (half_15_02_bounds6 i).2.1)
    (fun i => (half_15_02_bounds6 i).2.2) half_15_02_prefix
  convert h using 1 <;> norm_num [half_15_02_total1, half_15_02_total2, half_15_02_total3, half_15_02_total4, half_15_02_total5, half_15_02_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_15_02_hF1 : SourcePowerBound
    (paddedMoment 16 0 1 64 half_15_02_φ6) (1717171793/500000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 16) (j := 6) (r := 0) (n := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_15_02_φ6
    (fun i => (half_15_02_bounds6 i).1) (fun i => (half_15_02_bounds6 i).2.1)
    (fun i => (half_15_02_bounds6 i).2.2) half_15_02_prefix
  convert h using 1 <;> norm_num [half_15_02_total1, half_15_02_total2, half_15_02_total3, half_15_02_total4, half_15_02_total5, half_15_02_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_15_02_hx6 : SourcePowerBound
    (powerBoxCross 16 9 64 half_15_02_φ6) (52121691179/5000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 9) (r := 1) (v := 2) (t := 13) (D := 64)
    (a := (3/26 : ℝ)) (b := (5/26 : ℝ)) (c := (9/13 : ℝ))
    (by norm_num) half_15_02_φ6 (by norm_num [half_15_02_total1, half_15_02_total2, half_15_02_total3, half_15_02_total4, half_15_02_total5, half_15_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_15_02_total1, half_15_02_total2, half_15_02_total3, half_15_02_total4, half_15_02_total5, half_15_02_total6, parameterExponent, curveLoss, dyadicExponent]) half_15_02_hF1 half_15_02_hF2
    (SeedCompletionHigher16SimpleSeeds.degree16_half_13)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_02_total1, half_15_02_total2, half_15_02_total3, half_15_02_total4, half_15_02_total5, half_15_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_02_hx5 : SourcePowerBound
    (powerBoxCross 16 10 32 half_15_02_φ5) (112270224759/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 5) (s := 10) (u := 8) (t := 11)
    (D := 32) (ψ := (96395957/5000000000 : ℝ)) half_15_02_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_02_bounds5 l).1) (fun l => (half_15_02_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_02_total1, half_15_02_total2, half_15_02_total3, half_15_02_total4, half_15_02_total5, half_15_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_9) (SeedCompletionHigher16SimpleSeeds.degree16_half_11)
    (by simpa only [half_15_02_φ6, show (2:ℝ)*32=64 by norm_num] using half_15_02_hx6)
  exact h.weaken (by norm_num [half_15_02_total1, half_15_02_total2, half_15_02_total3, half_15_02_total4, half_15_02_total5, half_15_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_02_hx4 : SourcePowerBound
    (powerBoxCross 16 11 16 half_15_02_φ4) (62020169507/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (23127823/625000000 : ℝ)) half_15_02_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_02_bounds4 l).1) (fun l => (half_15_02_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_02_total1, half_15_02_total2, half_15_02_total3, half_15_02_total4, half_15_02_total5, half_15_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_10) (SeedCompletionHigher16SimpleSeeds.degree16_half_12)
    (by simpa only [half_15_02_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_02_hx5)
  exact h.weaken (by norm_num [half_15_02_total1, half_15_02_total2, half_15_02_total3, half_15_02_total4, half_15_02_total5, half_15_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_02_hx3 : SourcePowerBound
    (powerBoxCross 16 12 8 half_15_02_φ3) (138190543421/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (421601477/10000000000 : ℝ)) half_15_02_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_02_bounds3 l).1) (fun l => (half_15_02_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_02_total1, half_15_02_total2, half_15_02_total3, half_15_02_total4, half_15_02_total5, half_15_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_11) (SeedCompletionHigher16SimpleSeeds.degree16_half_13)
    (by simpa only [half_15_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_02_hx4)
  exact h.weaken (by norm_num [half_15_02_total1, half_15_02_total2, half_15_02_total3, half_15_02_total4, half_15_02_total5, half_15_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_02_hx2 : SourcePowerBound
    (powerBoxCross 16 13 4 half_15_02_φ2) (154447822569/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (444546383/10000000000 : ℝ)) half_15_02_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_02_bounds2 l).1) (fun l => (half_15_02_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_02_total1, half_15_02_total2, half_15_02_total3, half_15_02_total4, half_15_02_total5, half_15_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_12) (SeedCompletionHigher16SimpleSeeds.degree16_half_14)
    (by simpa only [half_15_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_02_hx3)
  exact h.weaken (by norm_num [half_15_02_total1, half_15_02_total2, half_15_02_total3, half_15_02_total4, half_15_02_total5, half_15_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_02_hx1 : SourcePowerBound
    (powerBoxCross 16 14 2 half_15_02_φ1) (43261093069/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (459517679/10000000000 : ℝ)) half_15_02_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_02_bounds1 l).1) (fun l => (half_15_02_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_02_total1, half_15_02_total2, half_15_02_total3, half_15_02_total4, half_15_02_total5, half_15_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_13) (half_15_01)
    (by simpa only [half_15_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_02_hx2)
  exact h.weaken (by norm_num [half_15_02_total1, half_15_02_total2, half_15_02_total3, half_15_02_total4, half_15_02_total5, half_15_02_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_15_02 : AdmissibleExponent 16 30 (186236616961/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 13) (ψ := (97720331/2000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (SeedCompletionHigher16SimpleSeeds.degree16_half_14)
    (by simpa only [half_15_02_φ1] using half_15_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_02_total1, half_15_02_total2, half_15_02_total3, half_15_02_total4, half_15_02_total5, half_15_02_total6, parameterExponent, curveLoss, dyadicExponent])

theorem chord_74 : AdmissibleExponent 16 32 (405241209299/20000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 32) (t := (1/2 : ℝ))
    (half_15_02) (half_17_01)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_16_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (63259579/1250000000 : ℝ)

private theorem half_16_02_total1 : total half_16_02_φ1=(63259579/1250000000 : ℝ) := by
  norm_num [half_16_02_φ1,total,emptyPhi,Fin.snoc]

private theorem half_16_02_bounds1 : ∀ l,0≤half_16_02_φ1 l ∧ half_16_02_φ1 l≤1 ∧
    0≤shiftExponents 16 half_16_02_φ1 l :=
  alternate_bounds_snoc emptyPhi (63259579/1250000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_16_02_φ2 : Fin 2 → ℝ := Fin.snoc half_16_02_φ1 (59514477/1250000000 : ℝ)

private theorem half_16_02_total2 : total half_16_02_φ2=(15346757/156250000 : ℝ) := by
  change total (Fin.snoc half_16_02_φ1 (59514477/1250000000 : ℝ))=(15346757/156250000 : ℝ)
  rw [alternate_total_snoc,half_16_02_total1]
  norm_num

private theorem half_16_02_bounds2 : ∀ l,0≤half_16_02_φ2 l ∧ half_16_02_φ2 l≤1 ∧
    0≤shiftExponents 16 half_16_02_φ2 l :=
  alternate_bounds_snoc half_16_02_φ1 (59514477/1250000000 : ℝ) half_16_02_bounds1 (by norm_num)

private def half_16_02_φ3 : Fin 3 → ℝ := Fin.snoc half_16_02_φ2 (456842757/10000000000 : ℝ)

private theorem half_16_02_total3 : total half_16_02_φ3=(287807041/2000000000 : ℝ) := by
  change total (Fin.snoc half_16_02_φ2 (456842757/10000000000 : ℝ))=(287807041/2000000000 : ℝ)
  rw [alternate_total_snoc,half_16_02_total2]
  norm_num

private theorem half_16_02_bounds3 : ∀ l,0≤half_16_02_φ3 l ∧ half_16_02_φ3 l≤1 ∧
    0≤shiftExponents 16 half_16_02_φ3 l :=
  alternate_bounds_snoc half_16_02_φ2 (456842757/10000000000 : ℝ) half_16_02_bounds2 (by norm_num)

private def half_16_02_φ4 : Fin 4 → ℝ := Fin.snoc half_16_02_φ3 (437685429/10000000000 : ℝ)

private theorem half_16_02_total4 : total half_16_02_φ4=(938360317/5000000000 : ℝ) := by
  change total (Fin.snoc half_16_02_φ3 (437685429/10000000000 : ℝ))=(938360317/5000000000 : ℝ)
  rw [alternate_total_snoc,half_16_02_total3]
  norm_num

private theorem half_16_02_bounds4 : ∀ l,0≤half_16_02_φ4 l ∧ half_16_02_φ4 l≤1 ∧
    0≤shiftExponents 16 half_16_02_φ4 l :=
  alternate_bounds_snoc half_16_02_φ3 (437685429/10000000000 : ℝ) half_16_02_bounds3 (by norm_num)

private def half_16_02_φ5 : Fin 5 → ℝ := Fin.snoc half_16_02_φ4 (39984991/1000000000 : ℝ)

private theorem half_16_02_total5 : total half_16_02_φ5=(142285659/625000000 : ℝ) := by
  change total (Fin.snoc half_16_02_φ4 (39984991/1000000000 : ℝ))=(142285659/625000000 : ℝ)
  rw [alternate_total_snoc,half_16_02_total4]
  norm_num

private theorem half_16_02_bounds5 : ∀ l,0≤half_16_02_φ5 l ∧ half_16_02_φ5 l≤1 ∧
    0≤shiftExponents 16 half_16_02_φ5 l :=
  alternate_bounds_snoc half_16_02_φ4 (39984991/1000000000 : ℝ) half_16_02_bounds4 (by norm_num)

private def half_16_02_φ6 : Fin 6 → ℝ := Fin.snoc half_16_02_φ5 (291124149/10000000000 : ℝ)

private theorem half_16_02_total6 : total half_16_02_φ6=(2567694693/10000000000 : ℝ) := by
  change total (Fin.snoc half_16_02_φ5 (291124149/10000000000 : ℝ))=(2567694693/10000000000 : ℝ)
  rw [alternate_total_snoc,half_16_02_total5]
  norm_num

private theorem half_16_02_bounds6 : ∀ l,0≤half_16_02_φ6 l ∧ half_16_02_φ6 l≤1 ∧
    0≤shiftExponents 16 half_16_02_φ6 l :=
  alternate_bounds_snoc half_16_02_φ5 (291124149/10000000000 : ℝ) half_16_02_bounds5 (by norm_num)

private theorem half_16_02_prefix : PrefixCondition 16 half_16_02_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, half_16_02_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_16_02_hF2 : SourcePowerBound
    (paddedMoment 16 0 2 64 half_16_02_φ6) (16890747763/2000000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 16) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_16_02_φ6
    (fun i => (half_16_02_bounds6 i).1) (fun i => (half_16_02_bounds6 i).2.1)
    (fun i => (half_16_02_bounds6 i).2.2) half_16_02_prefix
  convert h using 1 <;> norm_num [half_16_02_total1, half_16_02_total2, half_16_02_total3, half_16_02_total4, half_16_02_total5, half_16_02_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_16_02_hx6 : SourcePowerBound
    (powerBoxCross 16 10 64 half_16_02_φ6) (55442721009/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 10) (r := 2) (v := 13) (w := 14) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_16_02_φ6 (by norm_num [half_16_02_total1, half_16_02_total2, half_16_02_total3, half_16_02_total4, half_16_02_total5, half_16_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_16_02_total1, half_16_02_total2, half_16_02_total3, half_16_02_total4, half_16_02_total5, half_16_02_total6, parameterExponent, curveLoss, dyadicExponent]) half_16_02_hF2
    (SeedCompletionHigher16SimpleSeeds.degree16_half_13) (SeedCompletionHigher16SimpleSeeds.degree16_half_14)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_02_total1, half_16_02_total2, half_16_02_total3, half_16_02_total4, half_16_02_total5, half_16_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_02_hx5 : SourcePowerBound
    (powerBoxCross 16 11 32 half_16_02_φ5) (7553465853/625000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 5) (s := 11) (u := 9) (t := 12)
    (D := 32) (ψ := (291124149/10000000000 : ℝ)) half_16_02_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_02_bounds5 l).1) (fun l => (half_16_02_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_02_total1, half_16_02_total2, half_16_02_total3, half_16_02_total4, half_16_02_total5, half_16_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_10) (SeedCompletionHigher16SimpleSeeds.degree16_half_12)
    (by simpa only [half_16_02_φ6, show (2:ℝ)*32=64 by norm_num] using half_16_02_hx6)
  exact h.weaken (by norm_num [half_16_02_total1, half_16_02_total2, half_16_02_total3, half_16_02_total4, half_16_02_total5, half_16_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_02_hx4 : SourcePowerBound
    (powerBoxCross 16 12 16 half_16_02_φ4) (133960781603/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (39984991/1000000000 : ℝ)) half_16_02_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_02_bounds4 l).1) (fun l => (half_16_02_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_02_total1, half_16_02_total2, half_16_02_total3, half_16_02_total4, half_16_02_total5, half_16_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_11) (SeedCompletionHigher16SimpleSeeds.degree16_half_13)
    (by simpa only [half_16_02_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_02_hx5)
  exact h.weaken (by norm_num [half_16_02_total1, half_16_02_total2, half_16_02_total3, half_16_02_total4, half_16_02_total5, half_16_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_02_hx3 : SourcePowerBound
    (powerBoxCross 16 13 8 half_16_02_φ3) (149377141397/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (437685429/10000000000 : ℝ)) half_16_02_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_02_bounds3 l).1) (fun l => (half_16_02_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_02_total1, half_16_02_total2, half_16_02_total3, half_16_02_total4, half_16_02_total5, half_16_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_12) (SeedCompletionHigher16SimpleSeeds.degree16_half_14)
    (by simpa only [half_16_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_02_hx4)
  exact h.weaken (by norm_num [half_16_02_total1, half_16_02_total2, half_16_02_total3, half_16_02_total4, half_16_02_total5, half_16_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_02_hx2 : SourcePowerBound
    (powerBoxCross 16 14 4 half_16_02_φ2) (83502480173/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (456842757/10000000000 : ℝ)) half_16_02_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_02_bounds2 l).1) (fun l => (half_16_02_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_02_total1, half_16_02_total2, half_16_02_total3, half_16_02_total4, half_16_02_total5, half_16_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_13) (half_15_02)
    (by simpa only [half_16_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_02_hx3)
  exact h.weaken (by norm_num [half_16_02_total1, half_16_02_total2, half_16_02_total3, half_16_02_total4, half_16_02_total5, half_16_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_02_hx1 : SourcePowerBound
    (powerBoxCross 16 15 2 half_16_02_φ1) (11707355851/625000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (59514477/1250000000 : ℝ)) half_16_02_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_02_bounds1 l).1) (fun l => (half_16_02_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_02_total1, half_16_02_total2, half_16_02_total3, half_16_02_total4, half_16_02_total5, half_16_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_14) (chord_74)
    (by simpa only [half_16_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_02_hx2)
  exact h.weaken (by norm_num [half_16_02_total1, half_16_02_total2, half_16_02_total3, half_16_02_total4, half_16_02_total5, half_16_02_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_16_02 : AdmissibleExponent 16 32 (25249239493/1250000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 14) (ψ := (63259579/1250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_15_02)
    (by simpa only [half_16_02_φ1] using half_16_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_02_total1, half_16_02_total2, half_16_02_total3, half_16_02_total4, half_16_02_total5, half_16_02_total6, parameterExponent, curveLoss, dyadicExponent])

theorem chord_75 : AdmissibleExponent 16 34 (437642584291/20000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 34) (t := (1/2 : ℝ))
    (half_16_02) (half_18_01)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_17_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (64633511/1250000000 : ℝ)

private theorem half_17_02_total1 : total half_17_02_φ1=(64633511/1250000000 : ℝ) := by
  norm_num [half_17_02_φ1,total,emptyPhi,Fin.snoc]

private theorem half_17_02_bounds1 : ∀ l,0≤half_17_02_φ1 l ∧ half_17_02_φ1 l≤1 ∧
    0≤shiftExponents 16 half_17_02_φ1 l :=
  alternate_bounds_snoc emptyPhi (64633511/1250000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_17_02_φ2 : Fin 2 → ℝ := Fin.snoc half_17_02_φ1 (12155563/250000000 : ℝ)

private theorem half_17_02_total2 : total half_17_02_φ2=(62705663/625000000 : ℝ) := by
  change total (Fin.snoc half_17_02_φ1 (12155563/250000000 : ℝ))=(62705663/625000000 : ℝ)
  rw [alternate_total_snoc,half_17_02_total1]
  norm_num

private theorem half_17_02_bounds2 : ∀ l,0≤half_17_02_φ2 l ∧ half_17_02_φ2 l≤1 ∧
    0≤shiftExponents 16 half_17_02_φ2 l :=
  alternate_bounds_snoc half_17_02_φ1 (12155563/250000000 : ℝ) half_17_02_bounds1 (by norm_num)

private def half_17_02_φ3 : Fin 3 → ℝ := Fin.snoc half_17_02_φ2 (47436237/1000000000 : ℝ)

private theorem half_17_02_total3 : total half_17_02_φ3=(738826489/5000000000 : ℝ) := by
  change total (Fin.snoc half_17_02_φ2 (47436237/1000000000 : ℝ))=(738826489/5000000000 : ℝ)
  rw [alternate_total_snoc,half_17_02_total2]
  norm_num

private theorem half_17_02_bounds3 : ∀ l,0≤half_17_02_φ3 l ∧ half_17_02_φ3 l≤1 ∧
    0≤shiftExponents 16 half_17_02_φ3 l :=
  alternate_bounds_snoc half_17_02_φ2 (47436237/1000000000 : ℝ) half_17_02_bounds2 (by norm_num)

private def half_17_02_φ4 : Fin 4 → ℝ := Fin.snoc half_17_02_φ3 (113508227/2500000000 : ℝ)

private theorem half_17_02_total4 : total half_17_02_φ4=(965842943/5000000000 : ℝ) := by
  change total (Fin.snoc half_17_02_φ3 (113508227/2500000000 : ℝ))=(965842943/5000000000 : ℝ)
  rw [alternate_total_snoc,half_17_02_total3]
  norm_num

private theorem half_17_02_bounds4 : ∀ l,0≤half_17_02_φ4 l ∧ half_17_02_φ4 l≤1 ∧
    0≤shiftExponents 16 half_17_02_φ4 l :=
  alternate_bounds_snoc half_17_02_φ3 (113508227/2500000000 : ℝ) half_17_02_bounds3 (by norm_num)

private def half_17_02_φ5 : Fin 5 → ℝ := Fin.snoc half_17_02_φ4 (5379897/125000000 : ℝ)

private theorem half_17_02_total5 : total half_17_02_φ5=(1181038823/5000000000 : ℝ) := by
  change total (Fin.snoc half_17_02_φ4 (5379897/125000000 : ℝ))=(1181038823/5000000000 : ℝ)
  rw [alternate_total_snoc,half_17_02_total4]
  norm_num

private theorem half_17_02_bounds5 : ∀ l,0≤half_17_02_φ5 l ∧ half_17_02_φ5 l≤1 ∧
    0≤shiftExponents 16 half_17_02_φ5 l :=
  alternate_bounds_snoc half_17_02_φ4 (5379897/125000000 : ℝ) half_17_02_bounds4 (by norm_num)

private def half_17_02_φ6 : Fin 6 → ℝ := Fin.snoc half_17_02_φ5 (75320811/2000000000 : ℝ)

private theorem half_17_02_total6 : total half_17_02_φ6=(2738681701/10000000000 : ℝ) := by
  change total (Fin.snoc half_17_02_φ5 (75320811/2000000000 : ℝ))=(2738681701/10000000000 : ℝ)
  rw [alternate_total_snoc,half_17_02_total5]
  norm_num

private theorem half_17_02_bounds6 : ∀ l,0≤half_17_02_φ6 l ∧ half_17_02_φ6 l≤1 ∧
    0≤shiftExponents 16 half_17_02_φ6 l :=
  alternate_bounds_snoc half_17_02_φ5 (75320811/2000000000 : ℝ) half_17_02_bounds5 (by norm_num)

private def half_17_02_φ7 : Fin 7 → ℝ := Fin.snoc half_17_02_φ6 (206640873/10000000000 : ℝ)

private theorem half_17_02_total7 : total half_17_02_φ7=(1472661287/5000000000 : ℝ) := by
  change total (Fin.snoc half_17_02_φ6 (206640873/10000000000 : ℝ))=(1472661287/5000000000 : ℝ)
  rw [alternate_total_snoc,half_17_02_total6]
  norm_num

private theorem half_17_02_bounds7 : ∀ l,0≤half_17_02_φ7 l ∧ half_17_02_φ7 l≤1 ∧
    0≤shiftExponents 16 half_17_02_φ7 l :=
  alternate_bounds_snoc half_17_02_φ6 (206640873/10000000000 : ℝ) half_17_02_bounds6 (by norm_num)

private theorem half_17_02_prefix : PrefixCondition 16 half_17_02_φ7 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, half_17_02_φ6, half_17_02_φ7, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_17_02_hF2 : SourcePowerBound
    (paddedMoment 16 0 2 128 half_17_02_φ7) (9746048417/1000000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 16) (j := 7) (r := 0) (n := 1) (D := 128)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_17_02_φ7
    (fun i => (half_17_02_bounds7 i).1) (fun i => (half_17_02_bounds7 i).2.1)
    (fun i => (half_17_02_bounds7 i).2.2) half_17_02_prefix
  convert h using 1 <;> norm_num [half_17_02_total1, half_17_02_total2, half_17_02_total3, half_17_02_total4, half_17_02_total5, half_17_02_total6, half_17_02_total7, parameterExponent, curveLoss, dyadicExponent]

private theorem half_17_02_hF1 : SourcePowerBound
    (paddedMoment 16 0 1 128 half_17_02_φ7) (3582016139/1000000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 16) (j := 7) (r := 0) (n := 0) (D := 128)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_17_02_φ7
    (fun i => (half_17_02_bounds7 i).1) (fun i => (half_17_02_bounds7 i).2.1)
    (fun i => (half_17_02_bounds7 i).2.2) half_17_02_prefix
  convert h using 1 <;> norm_num [half_17_02_total1, half_17_02_total2, half_17_02_total3, half_17_02_total4, half_17_02_total5, half_17_02_total6, half_17_02_total7, parameterExponent, curveLoss, dyadicExponent]

private theorem half_17_02_hx7 : SourcePowerBound
    (powerBoxCross 16 10 128 half_17_02_φ7) (109563591961/10000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 10) (r := 1) (v := 2) (t := 14) (D := 128)
    (a := (1/14 : ℝ)) (b := (3/14 : ℝ)) (c := (5/7 : ℝ))
    (by norm_num) half_17_02_φ7 (by norm_num [half_17_02_total1, half_17_02_total2, half_17_02_total3, half_17_02_total4, half_17_02_total5, half_17_02_total6, half_17_02_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_17_02_total1, half_17_02_total2, half_17_02_total3, half_17_02_total4, half_17_02_total5, half_17_02_total6, half_17_02_total7, parameterExponent, curveLoss, dyadicExponent]) half_17_02_hF1 half_17_02_hF2
    (SeedCompletionHigher16SimpleSeeds.degree16_half_14)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_02_total1, half_17_02_total2, half_17_02_total3, half_17_02_total4, half_17_02_total5, half_17_02_total6, half_17_02_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_02_hx6 : SourcePowerBound
    (powerBoxCross 16 11 64 half_17_02_φ6) (7353249771/625000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 6) (s := 11) (u := 9) (t := 12)
    (D := 64) (ψ := (206640873/10000000000 : ℝ)) half_17_02_φ6
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_02_bounds6 l).1) (fun l => (half_17_02_bounds6 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_02_total1, half_17_02_total2, half_17_02_total3, half_17_02_total4, half_17_02_total5, half_17_02_total6, half_17_02_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_10) (SeedCompletionHigher16SimpleSeeds.degree16_half_12)
    (by simpa only [half_17_02_φ7, show (2:ℝ)*64=128 by norm_num] using half_17_02_hx7)
  exact h.weaken (by norm_num [half_17_02_total1, half_17_02_total2, half_17_02_total3, half_17_02_total4, half_17_02_total5, half_17_02_total6, half_17_02_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_02_hx5 : SourcePowerBound
    (powerBoxCross 16 12 32 half_17_02_φ5) (8105382123/625000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 5) (s := 12) (u := 10) (t := 13)
    (D := 32) (ψ := (75320811/2000000000 : ℝ)) half_17_02_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_02_bounds5 l).1) (fun l => (half_17_02_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_02_total1, half_17_02_total2, half_17_02_total3, half_17_02_total4, half_17_02_total5, half_17_02_total6, half_17_02_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_11) (SeedCompletionHigher16SimpleSeeds.degree16_half_13)
    (by simpa only [half_17_02_φ6, show (2:ℝ)*32=64 by norm_num] using half_17_02_hx6)
  exact h.weaken (by norm_num [half_17_02_total1, half_17_02_total2, half_17_02_total3, half_17_02_total4, half_17_02_total5, half_17_02_total6, half_17_02_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_02_hx4 : SourcePowerBound
    (powerBoxCross 16 13 16 half_17_02_φ4) (36062798881/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (5379897/125000000 : ℝ)) half_17_02_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_02_bounds4 l).1) (fun l => (half_17_02_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_02_total1, half_17_02_total2, half_17_02_total3, half_17_02_total4, half_17_02_total5, half_17_02_total6, half_17_02_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_12) (SeedCompletionHigher16SimpleSeeds.degree16_half_14)
    (by simpa only [half_17_02_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_02_hx5)
  exact h.weaken (by norm_num [half_17_02_total1, half_17_02_total2, half_17_02_total3, half_17_02_total4, half_17_02_total5, half_17_02_total6, half_17_02_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_02_hx3 : SourcePowerBound
    (powerBoxCross 16 14 8 half_17_02_φ3) (6443090627/400000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (113508227/2500000000 : ℝ)) half_17_02_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_02_bounds3 l).1) (fun l => (half_17_02_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_02_total1, half_17_02_total2, half_17_02_total3, half_17_02_total4, half_17_02_total5, half_17_02_total6, half_17_02_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_13) (half_15_02)
    (by simpa only [half_17_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_02_hx4)
  exact h.weaken (by norm_num [half_17_02_total1, half_17_02_total2, half_17_02_total3, half_17_02_total4, half_17_02_total5, half_17_02_total6, half_17_02_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_02_hx2 : SourcePowerBound
    (powerBoxCross 16 15 4 half_17_02_φ2) (45070468327/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (47436237/1000000000 : ℝ)) half_17_02_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_02_bounds2 l).1) (fun l => (half_17_02_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_02_total1, half_17_02_total2, half_17_02_total3, half_17_02_total4, half_17_02_total5, half_17_02_total6, half_17_02_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_14) (half_16_02)
    (by simpa only [half_17_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_02_hx3)
  exact h.weaken (by norm_num [half_17_02_total1, half_17_02_total2, half_17_02_total3, half_17_02_total4, half_17_02_total5, half_17_02_total6, half_17_02_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_02_hx1 : SourcePowerBound
    (powerBoxCross 16 16 2 half_17_02_φ1) (808266093/40000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (12155563/250000000 : ℝ)) half_17_02_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_02_bounds1 l).1) (fun l => (half_17_02_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_02_total1, half_17_02_total2, half_17_02_total3, half_17_02_total4, half_17_02_total5, half_17_02_total6, half_17_02_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_02) (chord_75)
    (by simpa only [half_17_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_02_hx2)
  exact h.weaken (by norm_num [half_17_02_total1, half_17_02_total2, half_17_02_total3, half_17_02_total4, half_17_02_total5, half_17_02_total6, half_17_02_total7, parameterExponent, curveLoss, dyadicExponent])

theorem half_17_02 : AdmissibleExponent 16 34 (109047816989/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 15) (ψ := (64633511/1250000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_16_02)
    (by simpa only [half_17_02_φ1] using half_17_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_02_total1, half_17_02_total2, half_17_02_total3, half_17_02_total4, half_17_02_total5, half_17_02_total6, half_17_02_total7, parameterExponent, curveLoss, dyadicExponent])

theorem chord_76 : AdmissibleExponent 16 36 (70592120129/3000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 36) (t := (2/3 : ℝ))
    (half_17_02) (half_20_01)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_18_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (527667813/10000000000 : ℝ)

private theorem half_18_02_total1 : total half_18_02_φ1=(527667813/10000000000 : ℝ) := by
  norm_num [half_18_02_φ1,total,emptyPhi,Fin.snoc]

private theorem half_18_02_bounds1 : ∀ l,0≤half_18_02_φ1 l ∧ half_18_02_φ1 l≤1 ∧
    0≤shiftExponents 16 half_18_02_φ1 l :=
  alternate_bounds_snoc emptyPhi (527667813/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_18_02_φ2 : Fin 2 → ℝ := Fin.snoc half_18_02_φ1 (247199587/5000000000 : ℝ)

private theorem half_18_02_total2 : total half_18_02_φ2=(1022066987/10000000000 : ℝ) := by
  change total (Fin.snoc half_18_02_φ1 (247199587/5000000000 : ℝ))=(1022066987/10000000000 : ℝ)
  rw [alternate_total_snoc,half_18_02_total1]
  norm_num

private theorem half_18_02_bounds2 : ∀ l,0≤half_18_02_φ2 l ∧ half_18_02_φ2 l≤1 ∧
    0≤shiftExponents 16 half_18_02_φ2 l :=
  alternate_bounds_snoc half_18_02_φ1 (247199587/5000000000 : ℝ) half_18_02_bounds1 (by norm_num)

private def half_18_02_φ3 : Fin 3 → ℝ := Fin.snoc half_18_02_φ2 (121118859/2500000000 : ℝ)

private theorem half_18_02_total3 : total half_18_02_φ3=(1506542423/10000000000 : ℝ) := by
  change total (Fin.snoc half_18_02_φ2 (121118859/2500000000 : ℝ))=(1506542423/10000000000 : ℝ)
  rw [alternate_total_snoc,half_18_02_total2]
  norm_num

private theorem half_18_02_bounds3 : ∀ l,0≤half_18_02_φ3 l ∧ half_18_02_φ3 l≤1 ∧
    0≤shiftExponents 16 half_18_02_φ3 l :=
  alternate_bounds_snoc half_18_02_φ2 (121118859/2500000000 : ℝ) half_18_02_bounds2 (by norm_num)

private def half_18_02_φ4 : Fin 4 → ℝ := Fin.snoc half_18_02_φ3 (235603653/5000000000 : ℝ)

private theorem half_18_02_total4 : total half_18_02_φ4=(1977749729/10000000000 : ℝ) := by
  change total (Fin.snoc half_18_02_φ3 (235603653/5000000000 : ℝ))=(1977749729/10000000000 : ℝ)
  rw [alternate_total_snoc,half_18_02_total3]
  norm_num

private theorem half_18_02_bounds4 : ∀ l,0≤half_18_02_φ4 l ∧ half_18_02_φ4 l≤1 ∧
    0≤shiftExponents 16 half_18_02_φ4 l :=
  alternate_bounds_snoc half_18_02_φ3 (235603653/5000000000 : ℝ) half_18_02_bounds3 (by norm_num)

private def half_18_02_φ5 : Fin 5 → ℝ := Fin.snoc half_18_02_φ4 (111732421/2500000000 : ℝ)

private theorem half_18_02_total5 : total half_18_02_φ5=(2424679413/10000000000 : ℝ) := by
  change total (Fin.snoc half_18_02_φ4 (111732421/2500000000 : ℝ))=(2424679413/10000000000 : ℝ)
  rw [alternate_total_snoc,half_18_02_total4]
  norm_num

private theorem half_18_02_bounds5 : ∀ l,0≤half_18_02_φ5 l ∧ half_18_02_φ5 l≤1 ∧
    0≤shiftExponents 16 half_18_02_φ5 l :=
  alternate_bounds_snoc half_18_02_φ4 (111732421/2500000000 : ℝ) half_18_02_bounds4 (by norm_num)

private def half_18_02_φ6 : Fin 6 → ℝ := Fin.snoc half_18_02_φ5 (204561337/5000000000 : ℝ)

private theorem half_18_02_total6 : total half_18_02_φ6=(2833802087/10000000000 : ℝ) := by
  change total (Fin.snoc half_18_02_φ5 (204561337/5000000000 : ℝ))=(2833802087/10000000000 : ℝ)
  rw [alternate_total_snoc,half_18_02_total5]
  norm_num

private theorem half_18_02_bounds6 : ∀ l,0≤half_18_02_φ6 l ∧ half_18_02_φ6 l≤1 ∧
    0≤shiftExponents 16 half_18_02_φ6 l :=
  alternate_bounds_snoc half_18_02_φ5 (204561337/5000000000 : ℝ) half_18_02_bounds5 (by norm_num)

private def half_18_02_φ7 : Fin 7 → ℝ := Fin.snoc half_18_02_φ6 (304863739/10000000000 : ℝ)

private theorem half_18_02_total7 : total half_18_02_φ7=(1569332913/5000000000 : ℝ) := by
  change total (Fin.snoc half_18_02_φ6 (304863739/10000000000 : ℝ))=(1569332913/5000000000 : ℝ)
  rw [alternate_total_snoc,half_18_02_total6]
  norm_num

private theorem half_18_02_bounds7 : ∀ l,0≤half_18_02_φ7 l ∧ half_18_02_φ7 l≤1 ∧
    0≤shiftExponents 16 half_18_02_φ7 l :=
  alternate_bounds_snoc half_18_02_φ6 (304863739/10000000000 : ℝ) half_18_02_bounds6 (by norm_num)

private theorem half_18_02_prefix : PrefixCondition 16 half_18_02_φ7 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_18_02_φ1, half_18_02_φ2, half_18_02_φ3, half_18_02_φ4, half_18_02_φ5, half_18_02_φ6, half_18_02_φ7, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_18_02_hF2 : SourcePowerBound
    (paddedMoment 16 0 2 128 half_18_02_φ7) (8876003783/1000000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 16) (j := 7) (r := 0) (n := 1) (D := 128)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_18_02_φ7
    (fun i => (half_18_02_bounds7 i).1) (fun i => (half_18_02_bounds7 i).2.1)
    (fun i => (half_18_02_bounds7 i).2.2) half_18_02_prefix
  convert h using 1 <;> norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, half_18_02_total7, parameterExponent, curveLoss, dyadicExponent]

private theorem half_18_02_hx7 : SourcePowerBound
    (powerBoxCross 16 11 128 half_18_02_φ7) (115397720119/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 11) (r := 2) (v := 14) (w := 15) (D := 128)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_18_02_φ7 (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, half_18_02_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, half_18_02_total7, parameterExponent, curveLoss, dyadicExponent]) half_18_02_hF2
    (SeedCompletionHigher16SimpleSeeds.degree16_half_14) (half_15_02)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, half_18_02_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_02_hx6 : SourcePowerBound
    (powerBoxCross 16 12 64 half_18_02_φ6) (1255855047/100000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 6) (s := 12) (u := 10) (t := 13)
    (D := 64) (ψ := (304863739/10000000000 : ℝ)) half_18_02_φ6
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_02_bounds6 l).1) (fun l => (half_18_02_bounds6 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, half_18_02_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_11) (SeedCompletionHigher16SimpleSeeds.degree16_half_13)
    (by simpa only [half_18_02_φ7, show (2:ℝ)*64=128 by norm_num] using half_18_02_hx7)
  exact h.weaken (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, half_18_02_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_02_hx5 : SourcePowerBound
    (powerBoxCross 16 13 32 half_18_02_φ5) (139046060467/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 5) (s := 13) (u := 11) (t := 14)
    (D := 32) (ψ := (204561337/5000000000 : ℝ)) half_18_02_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_02_bounds5 l).1) (fun l => (half_18_02_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, half_18_02_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_12) (SeedCompletionHigher16SimpleSeeds.degree16_half_14)
    (by simpa only [half_18_02_φ6, show (2:ℝ)*32=64 by norm_num] using half_18_02_hx6)
  exact h.weaken (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, half_18_02_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_02_hx4 : SourcePowerBound
    (powerBoxCross 16 14 16 half_18_02_φ4) (154978365861/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 14) (u := 12) (t := 15)
    (D := 16) (ψ := (111732421/2500000000 : ℝ)) half_18_02_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_02_bounds4 l).1) (fun l => (half_18_02_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, half_18_02_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_13) (half_15_02)
    (by simpa only [half_18_02_φ5, show (2:ℝ)*16=32 by norm_num] using half_18_02_hx5)
  exact h.weaken (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, half_18_02_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_02_hx3 : SourcePowerBound
    (powerBoxCross 16 15 8 half_18_02_φ3) (10833296949/625000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 15) (u := 13) (t := 16)
    (D := 8) (ψ := (235603653/5000000000 : ℝ)) half_18_02_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_02_bounds3 l).1) (fun l => (half_18_02_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, half_18_02_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_14) (half_16_02)
    (by simpa only [half_18_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_18_02_hx4)
  exact h.weaken (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, half_18_02_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_02_hx2 : SourcePowerBound
    (powerBoxCross 16 16 4 half_18_02_φ2) (96964083313/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 16) (u := 14) (t := 17)
    (D := 4) (ψ := (121118859/2500000000 : ℝ)) half_18_02_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_02_bounds2 l).1) (fun l => (half_18_02_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, half_18_02_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_02) (half_17_02)
    (by simpa only [half_18_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_18_02_hx3)
  exact h.weaken (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, half_18_02_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_02_hx1 : SourcePowerBound
    (powerBoxCross 16 17 2 half_18_02_φ1) (217115097187/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 17) (u := 15) (t := 18)
    (D := 2) (ψ := (247199587/5000000000 : ℝ)) half_18_02_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_02_bounds1 l).1) (fun l => (half_18_02_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, half_18_02_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_02) (chord_76)
    (by simpa only [half_18_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_18_02_hx2)
  exact h.weaken (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, half_18_02_total7, parameterExponent, curveLoss, dyadicExponent])

theorem half_18_02 : AdmissibleExponent 16 36 (29316016877/1250000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 16) (ψ := (527667813/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_17_02)
    (by simpa only [half_18_02_φ1] using half_18_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, half_18_02_total7, parameterExponent, curveLoss, dyadicExponent])

theorem chord_78 : AdmissibleExponent 16 38 (75618278297/3000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 38) (t := (2/3 : ℝ))
    (half_18_02) (half_21_01)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_19_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (536916531/10000000000 : ℝ)

private theorem half_19_02_total1 : total half_19_02_φ1=(536916531/10000000000 : ℝ) := by
  norm_num [half_19_02_φ1,total,emptyPhi,Fin.snoc]

private theorem half_19_02_bounds1 : ∀ l,0≤half_19_02_φ1 l ∧ half_19_02_φ1 l≤1 ∧
    0≤shiftExponents 16 half_19_02_φ1 l :=
  alternate_bounds_snoc emptyPhi (536916531/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_19_02_φ2 : Fin 2 → ℝ := Fin.snoc half_19_02_φ1 (125920713/2500000000 : ℝ)

private theorem half_19_02_total2 : total half_19_02_φ2=(1040599383/10000000000 : ℝ) := by
  change total (Fin.snoc half_19_02_φ1 (125920713/2500000000 : ℝ))=(1040599383/10000000000 : ℝ)
  rw [alternate_total_snoc,half_19_02_total1]
  norm_num

private theorem half_19_02_bounds2 : ∀ l,0≤half_19_02_φ2 l ∧ half_19_02_φ2 l≤1 ∧
    0≤shiftExponents 16 half_19_02_φ2 l :=
  alternate_bounds_snoc half_19_02_φ1 (125920713/2500000000 : ℝ) half_19_02_bounds1 (by norm_num)

private def half_19_02_φ3 : Fin 3 → ℝ := Fin.snoc half_19_02_φ2 (98664227/2000000000 : ℝ)

private theorem half_19_02_total3 : total half_19_02_φ3=(766960259/5000000000 : ℝ) := by
  change total (Fin.snoc half_19_02_φ2 (98664227/2000000000 : ℝ))=(766960259/5000000000 : ℝ)
  rw [alternate_total_snoc,half_19_02_total2]
  norm_num

private theorem half_19_02_bounds3 : ∀ l,0≤half_19_02_φ3 l ∧ half_19_02_φ3 l≤1 ∧
    0≤shiftExponents 16 half_19_02_φ3 l :=
  alternate_bounds_snoc half_19_02_φ2 (98664227/2000000000 : ℝ) half_19_02_bounds2 (by norm_num)

private def half_19_02_φ4 : Fin 4 → ℝ := Fin.snoc half_19_02_φ3 (96598541/2000000000 : ℝ)

private theorem half_19_02_total4 : total half_19_02_φ4=(2016913223/10000000000 : ℝ) := by
  change total (Fin.snoc half_19_02_φ3 (96598541/2000000000 : ℝ))=(2016913223/10000000000 : ℝ)
  rw [alternate_total_snoc,half_19_02_total3]
  norm_num

private theorem half_19_02_bounds4 : ∀ l,0≤half_19_02_φ4 l ∧ half_19_02_φ4 l≤1 ∧
    0≤shiftExponents 16 half_19_02_φ4 l :=
  alternate_bounds_snoc half_19_02_φ3 (96598541/2000000000 : ℝ) half_19_02_bounds3 (by norm_num)

private def half_19_02_φ5 : Fin 5 → ℝ := Fin.snoc half_19_02_φ4 (234427761/5000000000 : ℝ)

private theorem half_19_02_total5 : total half_19_02_φ5=(497153749/2000000000 : ℝ) := by
  change total (Fin.snoc half_19_02_φ4 (234427761/5000000000 : ℝ))=(497153749/2000000000 : ℝ)
  rw [alternate_total_snoc,half_19_02_total4]
  norm_num

private theorem half_19_02_bounds5 : ∀ l,0≤half_19_02_φ5 l ∧ half_19_02_φ5 l≤1 ∧
    0≤shiftExponents 16 half_19_02_φ5 l :=
  alternate_bounds_snoc half_19_02_φ4 (234427761/5000000000 : ℝ) half_19_02_bounds4 (by norm_num)

private def half_19_02_φ6 : Fin 6 → ℝ := Fin.snoc half_19_02_φ5 (442342367/10000000000 : ℝ)

private theorem half_19_02_total6 : total half_19_02_φ6=(366013889/1250000000 : ℝ) := by
  change total (Fin.snoc half_19_02_φ5 (442342367/10000000000 : ℝ))=(366013889/1250000000 : ℝ)
  rw [alternate_total_snoc,half_19_02_total5]
  norm_num

private theorem half_19_02_bounds6 : ∀ l,0≤half_19_02_φ6 l ∧ half_19_02_φ6 l≤1 ∧
    0≤shiftExponents 16 half_19_02_φ6 l :=
  alternate_bounds_snoc half_19_02_φ5 (442342367/10000000000 : ℝ) half_19_02_bounds5 (by norm_num)

private def half_19_02_φ7 : Fin 7 → ℝ := Fin.snoc half_19_02_φ6 (396083177/10000000000 : ℝ)

private theorem half_19_02_total7 : total half_19_02_φ7=(3324194289/10000000000 : ℝ) := by
  change total (Fin.snoc half_19_02_φ6 (396083177/10000000000 : ℝ))=(3324194289/10000000000 : ℝ)
  rw [alternate_total_snoc,half_19_02_total6]
  norm_num

private theorem half_19_02_bounds7 : ∀ l,0≤half_19_02_φ7 l ∧ half_19_02_φ7 l≤1 ∧
    0≤shiftExponents 16 half_19_02_φ7 l :=
  alternate_bounds_snoc half_19_02_φ6 (396083177/10000000000 : ℝ) half_19_02_bounds6 (by norm_num)

private theorem half_19_02_prefix : PrefixCondition 16 half_19_02_φ7 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_19_02_φ1, half_19_02_φ2, half_19_02_φ3, half_19_02_φ4, half_19_02_φ5, half_19_02_φ6, half_19_02_φ7, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_19_02_hF4 : SourcePowerBound
    (paddedMoment 16 0 4 128 half_19_02_φ7) (38191919931/2000000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 16) (j := 7) (r := 0) (n := 2) (D := 128)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_19_02_φ7
    (fun i => (half_19_02_bounds7 i).1) (fun i => (half_19_02_bounds7 i).2.1)
    (fun i => (half_19_02_bounds7 i).2.2) half_19_02_prefix
  convert h using 1 <;> norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, half_19_02_total7, parameterExponent, curveLoss, dyadicExponent]

private theorem half_19_02_hF2 : SourcePowerBound
    (paddedMoment 16 0 2 128 half_19_02_φ7) (16082251399/2000000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 16) (j := 7) (r := 0) (n := 1) (D := 128)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_19_02_φ7
    (fun i => (half_19_02_bounds7 i).1) (fun i => (half_19_02_bounds7 i).2.1)
    (fun i => (half_19_02_bounds7 i).2.2) half_19_02_prefix
  convert h using 1 <;> norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, half_19_02_total7, parameterExponent, curveLoss, dyadicExponent]

private theorem half_19_02_hx7 : SourcePowerBound
    (powerBoxCross 16 12 128 half_19_02_φ7) (121072026221/10000000000 : ℝ) := by
  have h := full_B_cross_power (k := 16) (s := 12) (r := 2) (v := 4) (t := 15) (D := 128)
    (a := (3/20 : ℝ)) (b := (1/20 : ℝ)) (c := (4/5 : ℝ))
    (by norm_num) half_19_02_φ7 (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, half_19_02_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, half_19_02_total7, parameterExponent, curveLoss, dyadicExponent]) half_19_02_hF2 half_19_02_hF4
    (half_15_02)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, half_19_02_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_02_hx6 : SourcePowerBound
    (powerBoxCross 16 13 64 half_19_02_φ6) (133561647331/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 6) (s := 13) (u := 11) (t := 14)
    (D := 64) (ψ := (396083177/10000000000 : ℝ)) half_19_02_φ6
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_02_bounds6 l).1) (fun l => (half_19_02_bounds6 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, half_19_02_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_12) (SeedCompletionHigher16SimpleSeeds.degree16_half_14)
    (by simpa only [half_19_02_φ7, show (2:ℝ)*64=128 by norm_num] using half_19_02_hx7)
  exact h.weaken (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, half_19_02_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_02_hx5 : SourcePowerBound
    (powerBoxCross 16 14 32 half_19_02_φ5) (74319044033/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 5) (s := 14) (u := 12) (t := 15)
    (D := 32) (ψ := (442342367/10000000000 : ℝ)) half_19_02_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_02_bounds5 l).1) (fun l => (half_19_02_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, half_19_02_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_13) (half_15_02)
    (by simpa only [half_19_02_φ6, show (2:ℝ)*32=64 by norm_num] using half_19_02_hx6)
  exact h.weaken (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, half_19_02_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_02_hx4 : SourcePowerBound
    (powerBoxCross 16 15 16 half_19_02_φ4) (83074246189/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 15) (u := 13) (t := 16)
    (D := 16) (ψ := (234427761/5000000000 : ℝ)) half_19_02_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_02_bounds4 l).1) (fun l => (half_19_02_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, half_19_02_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_14) (half_16_02)
    (by simpa only [half_19_02_φ5, show (2:ℝ)*16=32 by norm_num] using half_19_02_hx5)
  exact h.weaken (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, half_19_02_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_02_hx3 : SourcePowerBound
    (powerBoxCross 16 16 8 half_19_02_φ3) (46473496281/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 16) (u := 14) (t := 17)
    (D := 8) (ψ := (96598541/2000000000 : ℝ)) half_19_02_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_02_bounds3 l).1) (fun l => (half_19_02_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, half_19_02_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_02) (half_17_02)
    (by simpa only [half_19_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_19_02_hx4)
  exact h.weaken (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, half_19_02_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_02_hx2 : SourcePowerBound
    (powerBoxCross 16 17 4 half_19_02_φ2) (207850550661/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 17) (u := 15) (t := 18)
    (D := 4) (ψ := (98664227/2000000000 : ℝ)) half_19_02_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_02_bounds2 l).1) (fun l => (half_19_02_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, half_19_02_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_02) (half_18_02)
    (by simpa only [half_19_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_19_02_hx3)
  exact h.weaken (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, half_19_02_total7, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_02_hx1 : SourcePowerBound
    (powerBoxCross 16 18 2 half_19_02_φ1) (232472848291/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 18) (u := 16) (t := 19)
    (D := 2) (ψ := (125920713/2500000000 : ℝ)) half_19_02_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_02_bounds1 l).1) (fun l => (half_19_02_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, half_19_02_total7, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_02) (chord_78)
    (by simpa only [half_19_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_19_02_hx2)
  exact h.weaken (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, half_19_02_total7, parameterExponent, curveLoss, dyadicExponent])

theorem half_19_02 : AdmissibleExponent 16 38 (62816231719/2500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 17) (ψ := (536916531/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_18_02)
    (by simpa only [half_19_02_φ1] using half_19_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, half_19_02_total7, parameterExponent, curveLoss, dyadicExponent])

theorem chord_80 : AdmissibleExponent 16 40 (403637236759/15000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 40) (t := (2/3 : ℝ))
    (half_19_02) (half_22_01)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_20_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (136422459/2500000000 : ℝ)

private theorem half_20_02_total1 : total half_20_02_φ1=(136422459/2500000000 : ℝ) := by
  norm_num [half_20_02_φ1,total,emptyPhi,Fin.snoc]

private theorem half_20_02_bounds1 : ∀ l,0≤half_20_02_φ1 l ∧ half_20_02_φ1 l≤1 ∧
    0≤shiftExponents 16 half_20_02_φ1 l :=
  alternate_bounds_snoc emptyPhi (136422459/2500000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_20_02_φ2 : Fin 2 → ℝ := Fin.snoc half_20_02_φ1 (256303279/5000000000 : ℝ)

private theorem half_20_02_total2 : total half_20_02_φ2=(529148197/5000000000 : ℝ) := by
  change total (Fin.snoc half_20_02_φ1 (256303279/5000000000 : ℝ))=(529148197/5000000000 : ℝ)
  rw [alternate_total_snoc,half_20_02_total1]
  norm_num

private theorem half_20_02_bounds2 : ∀ l,0≤half_20_02_φ2 l ∧ half_20_02_φ2 l≤1 ∧
    0≤shiftExponents 16 half_20_02_φ2 l :=
  alternate_bounds_snoc half_20_02_φ1 (256303279/5000000000 : ℝ) half_20_02_bounds1 (by norm_num)

private def half_20_02_φ3 : Fin 3 → ℝ := Fin.snoc half_20_02_φ2 (125740411/2500000000 : ℝ)

private theorem half_20_02_total3 : total half_20_02_φ3=(780629019/5000000000 : ℝ) := by
  change total (Fin.snoc half_20_02_φ2 (125740411/2500000000 : ℝ))=(780629019/5000000000 : ℝ)
  rw [alternate_total_snoc,half_20_02_total2]
  norm_num

private theorem half_20_02_bounds3 : ∀ l,0≤half_20_02_φ3 l ∧ half_20_02_φ3 l≤1 ∧
    0≤shiftExponents 16 half_20_02_φ3 l :=
  alternate_bounds_snoc half_20_02_φ2 (125740411/2500000000 : ℝ) half_20_02_bounds2 (by norm_num)

private def half_20_02_φ4 : Fin 4 → ℝ := Fin.snoc half_20_02_φ3 (492824877/10000000000 : ℝ)

private theorem half_20_02_total4 : total half_20_02_φ4=(410816583/2000000000 : ℝ) := by
  change total (Fin.snoc half_20_02_φ3 (492824877/10000000000 : ℝ))=(410816583/2000000000 : ℝ)
  rw [alternate_total_snoc,half_20_02_total3]
  norm_num

private theorem half_20_02_bounds4 : ∀ l,0≤half_20_02_φ4 l ∧ half_20_02_φ4 l≤1 ∧
    0≤shiftExponents 16 half_20_02_φ4 l :=
  alternate_bounds_snoc half_20_02_φ3 (492824877/10000000000 : ℝ) half_20_02_bounds3 (by norm_num)

private def half_20_02_φ5 : Fin 5 → ℝ := Fin.snoc half_20_02_φ4 (120792899/2500000000 : ℝ)

private theorem half_20_02_total5 : total half_20_02_φ5=(2537254511/10000000000 : ℝ) := by
  change total (Fin.snoc half_20_02_φ4 (120792899/2500000000 : ℝ))=(2537254511/10000000000 : ℝ)
  rw [alternate_total_snoc,half_20_02_total4]
  norm_num

private theorem half_20_02_bounds5 : ∀ l,0≤half_20_02_φ5 l ∧ half_20_02_φ5 l≤1 ∧
    0≤shiftExponents 16 half_20_02_φ5 l :=
  alternate_bounds_snoc half_20_02_φ4 (120792899/2500000000 : ℝ) half_20_02_bounds4 (by norm_num)

private def half_20_02_φ6 : Fin 6 → ℝ := Fin.snoc half_20_02_φ5 (471416723/10000000000 : ℝ)

private theorem half_20_02_total6 : total half_20_02_φ6=(1504335617/5000000000 : ℝ) := by
  change total (Fin.snoc half_20_02_φ5 (471416723/10000000000 : ℝ))=(1504335617/5000000000 : ℝ)
  rw [alternate_total_snoc,half_20_02_total5]
  norm_num

private theorem half_20_02_bounds6 : ∀ l,0≤half_20_02_φ6 l ∧ half_20_02_φ6 l≤1 ∧
    0≤shiftExponents 16 half_20_02_φ6 l :=
  alternate_bounds_snoc half_20_02_φ5 (471416723/10000000000 : ℝ) half_20_02_bounds5 (by norm_num)

private def half_20_02_φ7 : Fin 7 → ℝ := Fin.snoc half_20_02_φ6 (226483569/5000000000 : ℝ)

private theorem half_20_02_total7 : total half_20_02_φ7=(865409593/2500000000 : ℝ) := by
  change total (Fin.snoc half_20_02_φ6 (226483569/5000000000 : ℝ))=(865409593/2500000000 : ℝ)
  rw [alternate_total_snoc,half_20_02_total6]
  norm_num

private theorem half_20_02_bounds7 : ∀ l,0≤half_20_02_φ7 l ∧ half_20_02_φ7 l≤1 ∧
    0≤shiftExponents 16 half_20_02_φ7 l :=
  alternate_bounds_snoc half_20_02_φ6 (226483569/5000000000 : ℝ) half_20_02_bounds6 (by norm_num)

private def half_20_02_φ8 : Fin 8 → ℝ := Fin.snoc half_20_02_φ7 (432678533/10000000000 : ℝ)

private theorem half_20_02_total8 : total half_20_02_φ8=(778863381/2000000000 : ℝ) := by
  change total (Fin.snoc half_20_02_φ7 (432678533/10000000000 : ℝ))=(778863381/2000000000 : ℝ)
  rw [alternate_total_snoc,half_20_02_total7]
  norm_num

private theorem half_20_02_bounds8 : ∀ l,0≤half_20_02_φ8 l ∧ half_20_02_φ8 l≤1 ∧
    0≤shiftExponents 16 half_20_02_φ8 l :=
  alternate_bounds_snoc half_20_02_φ7 (432678533/10000000000 : ℝ) half_20_02_bounds7 (by norm_num)

private def half_20_02_φ9 : Fin 9 → ℝ := Fin.snoc half_20_02_φ8 (24434287/625000000 : ℝ)

private theorem half_20_02_total9 : total half_20_02_φ9=(4285265497/10000000000 : ℝ) := by
  change total (Fin.snoc half_20_02_φ8 (24434287/625000000 : ℝ))=(4285265497/10000000000 : ℝ)
  rw [alternate_total_snoc,half_20_02_total8]
  norm_num

private theorem half_20_02_bounds9 : ∀ l,0≤half_20_02_φ9 l ∧ half_20_02_φ9 l≤1 ∧
    0≤shiftExponents 16 half_20_02_φ9 l :=
  alternate_bounds_snoc half_20_02_φ8 (24434287/625000000 : ℝ) half_20_02_bounds8 (by norm_num)

private theorem half_20_02_prefix : PrefixCondition 16 half_20_02_φ9 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_20_02_φ1, half_20_02_φ2, half_20_02_φ3, half_20_02_φ4, half_20_02_φ5, half_20_02_φ6, half_20_02_φ7, half_20_02_φ8, half_20_02_φ9, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_20_02_hF1 : SourcePowerBound
    (paddedMoment 16 0 1 512 half_20_02_φ9) (7144203509/2000000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 16) (j := 9) (r := 0) (n := 0) (D := 512)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_20_02_φ9
    (fun i => (half_20_02_bounds9 i).1) (fun i => (half_20_02_bounds9 i).2.1)
    (fun i => (half_20_02_bounds9 i).2.2) half_20_02_prefix
  convert h using 1 <;> norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, half_20_02_total7, half_20_02_total8, half_20_02_total9, parameterExponent, curveLoss, dyadicExponent]

private theorem half_20_02_hx9 : SourcePowerBound
    (powerBoxCross 16 11 512 half_20_02_φ9) (3279288701/312500000 : ℝ) := by
  have h := full_A_cross_power (k := 16) (s := 11) (r := 1) (v := 0) (w := 22) (D := 512)
    (a := (1/2 : ℝ)) (b := (0/1 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_20_02_φ9 (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, half_20_02_total7, half_20_02_total8, half_20_02_total9, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, half_20_02_total7, half_20_02_total8, half_20_02_total9, parameterExponent, curveLoss, dyadicExponent]) half_20_02_hF1
    (admissibleExponent_zero 16) (half_22_01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, half_20_02_total7, half_20_02_total8, half_20_02_total9, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_02_hx8 : SourcePowerBound
    (powerBoxCross 16 12 256 half_20_02_φ8) (14378368999/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 8) (s := 12) (u := 10) (t := 13)
    (D := 256) (ψ := (24434287/625000000 : ℝ)) half_20_02_φ8
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_02_bounds8 l).1) (fun l => (half_20_02_bounds8 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, half_20_02_total7, half_20_02_total8, half_20_02_total9, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_11) (SeedCompletionHigher16SimpleSeeds.degree16_half_13)
    (by simpa only [half_20_02_φ9, show (2:ℝ)*256=512 by norm_num] using half_20_02_hx9)
  exact h.weaken (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, half_20_02_total7, half_20_02_total8, half_20_02_total9, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_02_hx7 : SourcePowerBound
    (powerBoxCross 16 13 128 half_20_02_φ7) (31849836101/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 7) (s := 13) (u := 11) (t := 14)
    (D := 128) (ψ := (432678533/10000000000 : ℝ)) half_20_02_φ7
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_02_bounds7 l).1) (fun l => (half_20_02_bounds7 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, half_20_02_total7, half_20_02_total8, half_20_02_total9, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_12) (SeedCompletionHigher16SimpleSeeds.degree16_half_14)
    (by simpa only [half_20_02_φ8, show (2:ℝ)*128=256 by norm_num] using half_20_02_hx8)
  exact h.weaken (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, half_20_02_total7, half_20_02_total8, half_20_02_total9, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_02_hx6 : SourcePowerBound
    (powerBoxCross 16 14 64 half_20_02_φ6) (28379759609/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 6) (s := 14) (u := 12) (t := 15)
    (D := 64) (ψ := (226483569/5000000000 : ℝ)) half_20_02_φ6
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_02_bounds6 l).1) (fun l => (half_20_02_bounds6 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, half_20_02_total7, half_20_02_total8, half_20_02_total9, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_13) (half_15_02)
    (by simpa only [half_20_02_φ7, show (2:ℝ)*64=128 by norm_num] using half_20_02_hx7)
  exact h.weaken (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, half_20_02_total7, half_20_02_total8, half_20_02_total9, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_02_hx5 : SourcePowerBound
    (powerBoxCross 16 15 32 half_20_02_φ5) (79327787601/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 5) (s := 15) (u := 13) (t := 16)
    (D := 32) (ψ := (471416723/10000000000 : ℝ)) half_20_02_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_02_bounds5 l).1) (fun l => (half_20_02_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, half_20_02_total7, half_20_02_total8, half_20_02_total9, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher16SimpleSeeds.degree16_half_14) (half_16_02)
    (by simpa only [half_20_02_φ6, show (2:ℝ)*32=64 by norm_num] using half_20_02_hx6)
  exact h.weaken (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, half_20_02_total7, half_20_02_total8, half_20_02_total9, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_02_hx4 : SourcePowerBound
    (powerBoxCross 16 16 16 half_20_02_φ4) (17757664509/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 4) (s := 16) (u := 14) (t := 17)
    (D := 16) (ψ := (120792899/2500000000 : ℝ)) half_20_02_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_02_bounds4 l).1) (fun l => (half_20_02_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, half_20_02_total7, half_20_02_total8, half_20_02_total9, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_02) (half_17_02)
    (by simpa only [half_20_02_φ5, show (2:ℝ)*16=32 by norm_num] using half_20_02_hx5)
  exact h.weaken (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, half_20_02_total7, half_20_02_total8, half_20_02_total9, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_02_hx3 : SourcePowerBound
    (powerBoxCross 16 17 8 half_20_02_φ3) (39734758713/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 3) (s := 17) (u := 15) (t := 18)
    (D := 8) (ψ := (492824877/10000000000 : ℝ)) half_20_02_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_02_bounds3 l).1) (fun l => (half_20_02_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, half_20_02_total7, half_20_02_total8, half_20_02_total9, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_02) (half_18_02)
    (by simpa only [half_20_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_20_02_hx4)
  exact h.weaken (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, half_20_02_total7, half_20_02_total8, half_20_02_total9, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_02_hx2 : SourcePowerBound
    (powerBoxCross 16 18 4 half_20_02_φ2) (222035366089/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 2) (s := 18) (u := 16) (t := 19)
    (D := 4) (ψ := (125740411/2500000000 : ℝ)) half_20_02_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_02_bounds2 l).1) (fun l => (half_20_02_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, half_20_02_total7, half_20_02_total8, half_20_02_total9, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_02) (half_19_02)
    (by simpa only [half_20_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_20_02_hx3)
  exact h.weaken (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, half_20_02_total7, half_20_02_total8, half_20_02_total9, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_02_hx1 : SourcePowerBound
    (powerBoxCross 16 19 2 half_20_02_φ1) (124049672521/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 16) (j := 1) (s := 19) (u := 17) (t := 20)
    (D := 2) (ψ := (256303279/5000000000 : ℝ)) half_20_02_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_02_bounds1 l).1) (fun l => (half_20_02_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, half_20_02_total7, half_20_02_total8, half_20_02_total9, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_02) (chord_80)
    (by simpa only [half_20_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_20_02_hx2)
  exact h.weaken (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, half_20_02_total7, half_20_02_total8, half_20_02_total9, parameterExponent, curveLoss, dyadicExponent])

theorem half_20_02 : AdmissibleExponent 16 40 (134144934487/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 16) (s := 18) (ψ := (136422459/2500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_19_02)
    (by simpa only [half_20_02_φ1] using half_20_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, half_20_02_total7, half_20_02_total8, half_20_02_total9, parameterExponent, curveLoss, dyadicExponent])

theorem chord_82 : AdmissibleExponent 16 42 (143186950333/5000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 42) (t := (3/4 : ℝ))
    (half_20_02) (half_24_01)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

#print axioms chord_82
end Waring.SeedCompletionAlternate16Seeds
