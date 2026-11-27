import Waring.SeedCompletionAlternate9Steps09

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionAlternate9Seeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges SeedCompletionDivisorPowerScales
open PolicyCompletionSharpResidualSource

private def half_14_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (999600541/10000000000 : ℝ)

private theorem half_14_09_total1 : total half_14_09_φ1=(999600541/10000000000 : ℝ) := by
  norm_num [half_14_09_φ1,total,emptyPhi,Fin.snoc]

private theorem half_14_09_bounds1 : ∀ l,0≤half_14_09_φ1 l ∧ half_14_09_φ1 l≤1 ∧
    0≤shiftExponents 9 half_14_09_φ1 l :=
  alternate_bounds_snoc emptyPhi (999600541/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_14_09_φ2 : Fin 2 → ℝ := Fin.snoc half_14_09_φ1 (965280123/10000000000 : ℝ)

private theorem half_14_09_total2 : total half_14_09_φ2=(245610083/1250000000 : ℝ) := by
  change total (Fin.snoc half_14_09_φ1 (965280123/10000000000 : ℝ))=(245610083/1250000000 : ℝ)
  rw [alternate_total_snoc,half_14_09_total1]
  norm_num

private theorem half_14_09_bounds2 : ∀ l,0≤half_14_09_φ2 l ∧ half_14_09_φ2 l≤1 ∧
    0≤shiftExponents 9 half_14_09_φ2 l :=
  alternate_bounds_snoc half_14_09_φ1 (965280123/10000000000 : ℝ) half_14_09_bounds1 (by norm_num)

private def half_14_09_φ3 : Fin 3 → ℝ := Fin.snoc half_14_09_φ2 (460344849/5000000000 : ℝ)

private theorem half_14_09_total3 : total half_14_09_φ3=(1442785181/5000000000 : ℝ) := by
  change total (Fin.snoc half_14_09_φ2 (460344849/5000000000 : ℝ))=(1442785181/5000000000 : ℝ)
  rw [alternate_total_snoc,half_14_09_total2]
  norm_num

private theorem half_14_09_bounds3 : ∀ l,0≤half_14_09_φ3 l ∧ half_14_09_φ3 l≤1 ∧
    0≤shiftExponents 9 half_14_09_φ3 l :=
  alternate_bounds_snoc half_14_09_φ2 (460344849/5000000000 : ℝ) half_14_09_bounds2 (by norm_num)

private def half_14_09_φ4 : Fin 4 → ℝ := Fin.snoc half_14_09_φ3 (213164787/2500000000 : ℝ)

private theorem half_14_09_total4 : total half_14_09_φ4=(373822951/1000000000 : ℝ) := by
  change total (Fin.snoc half_14_09_φ3 (213164787/2500000000 : ℝ))=(373822951/1000000000 : ℝ)
  rw [alternate_total_snoc,half_14_09_total3]
  norm_num

private theorem half_14_09_bounds4 : ∀ l,0≤half_14_09_φ4 l ∧ half_14_09_φ4 l≤1 ∧
    0≤shiftExponents 9 half_14_09_φ4 l :=
  alternate_bounds_snoc half_14_09_φ3 (213164787/2500000000 : ℝ) half_14_09_bounds3 (by norm_num)

private def half_14_09_φ5 : Fin 5 → ℝ := Fin.snoc half_14_09_φ4 (724661961/10000000000 : ℝ)

private theorem half_14_09_total5 : total half_14_09_φ5=(4462891471/10000000000 : ℝ) := by
  change total (Fin.snoc half_14_09_φ4 (724661961/10000000000 : ℝ))=(4462891471/10000000000 : ℝ)
  rw [alternate_total_snoc,half_14_09_total4]
  norm_num

private theorem half_14_09_bounds5 : ∀ l,0≤half_14_09_φ5 l ∧ half_14_09_φ5 l≤1 ∧
    0≤shiftExponents 9 half_14_09_φ5 l :=
  alternate_bounds_snoc half_14_09_φ4 (724661961/10000000000 : ℝ) half_14_09_bounds4 (by norm_num)

private def half_14_09_φ6 : Fin 6 → ℝ := Fin.snoc half_14_09_φ5 (419393601/10000000000 : ℝ)

private theorem half_14_09_total6 : total half_14_09_φ6=(305142817/625000000 : ℝ) := by
  change total (Fin.snoc half_14_09_φ5 (419393601/10000000000 : ℝ))=(305142817/625000000 : ℝ)
  rw [alternate_total_snoc,half_14_09_total5]
  norm_num

private theorem half_14_09_bounds6 : ∀ l,0≤half_14_09_φ6 l ∧ half_14_09_φ6 l≤1 ∧
    0≤shiftExponents 9 half_14_09_φ6 l :=
  alternate_bounds_snoc half_14_09_φ5 (419393601/10000000000 : ℝ) half_14_09_bounds5 (by norm_num)

private theorem half_14_09_prefix : PrefixCondition 9 half_14_09_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_14_09_φ1, half_14_09_φ2, half_14_09_φ3, half_14_09_φ4, half_14_09_φ5, half_14_09_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_14_09_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_14_09_φ6) (647071549/78125000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_14_09_φ6
    (fun i => (half_14_09_bounds6 i).1) (fun i => (half_14_09_bounds6 i).2.1)
    (fun i => (half_14_09_bounds6 i).2.2) half_14_09_prefix
  convert h using 1 <;> norm_num [half_14_09_total1, half_14_09_total2, half_14_09_total3, half_14_09_total4, half_14_09_total5, half_14_09_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_14_09_hF1 : SourcePowerBound
    (paddedMoment 9 0 1 64 half_14_09_φ6) (241732183/78125000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_14_09_φ6
    (fun i => (half_14_09_bounds6 i).1) (fun i => (half_14_09_bounds6 i).2.1)
    (fun i => (half_14_09_bounds6 i).2.2) half_14_09_prefix
  convert h using 1 <;> norm_num [half_14_09_total1, half_14_09_total2, half_14_09_total3, half_14_09_total4, half_14_09_total5, half_14_09_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_14_09_hx6 : SourcePowerBound
    (powerBoxCross 9 8 64 half_14_09_φ6) (14773284483/2000000000 : ℝ) := by
  have h := full_B_cross_power (k := 9) (s := 8) (r := 1) (v := 2) (t := 11) (D := 64)
    (a := (1/22 : ℝ)) (b := (5/22 : ℝ)) (c := (8/11 : ℝ))
    (by norm_num) half_14_09_φ6 (by norm_num [half_14_09_total1, half_14_09_total2, half_14_09_total3, half_14_09_total4, half_14_09_total5, half_14_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_14_09_total1, half_14_09_total2, half_14_09_total3, half_14_09_total4, half_14_09_total5, half_14_09_total6, parameterExponent, curveLoss, dyadicExponent]) half_14_09_hF1 half_14_09_hF2
    (half_11_09)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_09_total1, half_14_09_total2, half_14_09_total3, half_14_09_total4, half_14_09_total5, half_14_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_09_hx5 : SourcePowerBound
    (powerBoxCross 9 9 32 half_14_09_φ5) (41258035973/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 9) (u := 7) (t := 10)
    (D := 32) (ψ := (419393601/10000000000 : ℝ)) half_14_09_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_09_bounds5 l).1) (fun l => (half_14_09_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_09_total1, half_14_09_total2, half_14_09_total3, half_14_09_total4, half_14_09_total5, half_14_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_09)
    (by simpa only [half_14_09_φ6, show (2:ℝ)*32=64 by norm_num] using half_14_09_hx6)
  exact h.weaken (by norm_num [half_14_09_total1, half_14_09_total2, half_14_09_total3, half_14_09_total4, half_14_09_total5, half_14_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_09_hx4 : SourcePowerBound
    (powerBoxCross 9 10 16 half_14_09_φ4) (97582843869/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (724661961/10000000000 : ℝ)) half_14_09_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_09_bounds4 l).1) (fun l => (half_14_09_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_09_total1, half_14_09_total2, half_14_09_total3, half_14_09_total4, half_14_09_total5, half_14_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_09)
    (by simpa only [half_14_09_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_09_hx5)
  exact h.weaken (by norm_num [half_14_09_total1, half_14_09_total2, half_14_09_total3, half_14_09_total4, half_14_09_total5, half_14_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_09_hx3 : SourcePowerBound
    (powerBoxCross 9 11 8 half_14_09_φ3) (29431304401/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (213164787/2500000000 : ℝ)) half_14_09_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_09_bounds3 l).1) (fun l => (half_14_09_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_09_total1, half_14_09_total2, half_14_09_total3, half_14_09_total4, half_14_09_total5, half_14_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_09) (half_12_09)
    (by simpa only [half_14_09_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_09_hx4)
  exact h.weaken (by norm_num [half_14_09_total1, half_14_09_total2, half_14_09_total3, half_14_09_total4, half_14_09_total5, half_14_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_09_hx2 : SourcePowerBound
    (powerBoxCross 9 12 4 half_14_09_φ2) (5702811917/400000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (460344849/5000000000 : ℝ)) half_14_09_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_09_bounds2 l).1) (fun l => (half_14_09_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_09_total1, half_14_09_total2, half_14_09_total3, half_14_09_total4, half_14_09_total5, half_14_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_09) (half_13_09)
    (by simpa only [half_14_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_09_hx3)
  exact h.weaken (by norm_num [half_14_09_total1, half_14_09_total2, half_14_09_total3, half_14_09_total4, half_14_09_total5, half_14_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_09_hx1 : SourcePowerBound
    (powerBoxCross 9 13 2 half_14_09_φ1) (172074607293/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (965280123/10000000000 : ℝ)) half_14_09_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_09_bounds1 l).1) (fun l => (half_14_09_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_09_total1, half_14_09_total2, half_14_09_total3, half_14_09_total4, half_14_09_total5, half_14_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_09) (half_14_08)
    (by simpa only [half_14_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_09_hx2)
  exact h.weaken (by norm_num [half_14_09_total1, half_14_09_total2, half_14_09_total3, half_14_09_total4, half_14_09_total5, half_14_09_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_14_09 : AdmissibleExponent 9 28 (98532310409/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 12) (ψ := (999600541/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_13_09)
    (by simpa only [half_14_09_φ1] using half_14_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_09_total1, half_14_09_total2, half_14_09_total3, half_14_09_total4, half_14_09_total5, half_14_09_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_15_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (63751607/625000000 : ℝ)

private theorem half_15_09_total1 : total half_15_09_φ1=(63751607/625000000 : ℝ) := by
  norm_num [half_15_09_φ1,total,emptyPhi,Fin.snoc]

private theorem half_15_09_bounds1 : ∀ l,0≤half_15_09_φ1 l ∧ half_15_09_φ1 l≤1 ∧
    0≤shiftExponents 9 half_15_09_φ1 l :=
  alternate_bounds_snoc emptyPhi (63751607/625000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_15_09_φ2 : Fin 2 → ℝ := Fin.snoc half_15_09_φ1 (990442403/10000000000 : ℝ)

private theorem half_15_09_total2 : total half_15_09_φ2=(402093623/2000000000 : ℝ) := by
  change total (Fin.snoc half_15_09_φ1 (990442403/10000000000 : ℝ))=(402093623/2000000000 : ℝ)
  rw [alternate_total_snoc,half_15_09_total1]
  norm_num

private theorem half_15_09_bounds2 : ∀ l,0≤half_15_09_φ2 l ∧ half_15_09_φ2 l≤1 ∧
    0≤shiftExponents 9 half_15_09_φ2 l :=
  alternate_bounds_snoc half_15_09_φ1 (990442403/10000000000 : ℝ) half_15_09_bounds1 (by norm_num)

private def half_15_09_φ3 : Fin 3 → ℝ := Fin.snoc half_15_09_φ2 (950909431/10000000000 : ℝ)

private theorem half_15_09_total3 : total half_15_09_φ3=(1480688773/5000000000 : ℝ) := by
  change total (Fin.snoc half_15_09_φ2 (950909431/10000000000 : ℝ))=(1480688773/5000000000 : ℝ)
  rw [alternate_total_snoc,half_15_09_total2]
  norm_num

private theorem half_15_09_bounds3 : ∀ l,0≤half_15_09_φ3 l ∧ half_15_09_φ3 l≤1 ∧
    0≤shiftExponents 9 half_15_09_φ3 l :=
  alternate_bounds_snoc half_15_09_φ2 (950909431/10000000000 : ℝ) half_15_09_bounds2 (by norm_num)

private def half_15_09_φ4 : Fin 4 → ℝ := Fin.snoc half_15_09_φ3 (439913903/5000000000 : ℝ)

private theorem half_15_09_total4 : total half_15_09_φ4=(480150669/1250000000 : ℝ) := by
  change total (Fin.snoc half_15_09_φ3 (439913903/5000000000 : ℝ))=(480150669/1250000000 : ℝ)
  rw [alternate_total_snoc,half_15_09_total3]
  norm_num

private theorem half_15_09_bounds4 : ∀ l,0≤half_15_09_φ4 l ∧ half_15_09_φ4 l≤1 ∧
    0≤shiftExponents 9 half_15_09_φ4 l :=
  alternate_bounds_snoc half_15_09_φ3 (439913903/5000000000 : ℝ) half_15_09_bounds3 (by norm_num)

private def half_15_09_φ5 : Fin 5 → ℝ := Fin.snoc half_15_09_φ4 (76984933/1000000000 : ℝ)

private theorem half_15_09_total5 : total half_15_09_φ5=(2305527341/5000000000 : ℝ) := by
  change total (Fin.snoc half_15_09_φ4 (76984933/1000000000 : ℝ))=(2305527341/5000000000 : ℝ)
  rw [alternate_total_snoc,half_15_09_total4]
  norm_num

private theorem half_15_09_bounds5 : ∀ l,0≤half_15_09_φ5 l ∧ half_15_09_φ5 l≤1 ∧
    0≤shiftExponents 9 half_15_09_φ5 l :=
  alternate_bounds_snoc half_15_09_φ4 (76984933/1000000000 : ℝ) half_15_09_bounds4 (by norm_num)

private def half_15_09_φ6 : Fin 6 → ℝ := Fin.snoc half_15_09_φ5 (137223057/2500000000 : ℝ)

private theorem half_15_09_total6 : total half_15_09_φ6=(515994691/1000000000 : ℝ) := by
  change total (Fin.snoc half_15_09_φ5 (137223057/2500000000 : ℝ))=(515994691/1000000000 : ℝ)
  rw [alternate_total_snoc,half_15_09_total5]
  norm_num

private theorem half_15_09_bounds6 : ∀ l,0≤half_15_09_φ6 l ∧ half_15_09_φ6 l≤1 ∧
    0≤shiftExponents 9 half_15_09_φ6 l :=
  alternate_bounds_snoc half_15_09_φ5 (137223057/2500000000 : ℝ) half_15_09_bounds5 (by norm_num)

private theorem half_15_09_prefix : PrefixCondition 9 half_15_09_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_15_09_φ1, half_15_09_φ2, half_15_09_φ3, half_15_09_φ4, half_15_09_φ5, half_15_09_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_15_09_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_15_09_φ6) (952015927/125000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_15_09_φ6
    (fun i => (half_15_09_bounds6 i).1) (fun i => (half_15_09_bounds6 i).2.1)
    (fun i => (half_15_09_bounds6 i).2.2) half_15_09_prefix
  convert h using 1 <;> norm_num [half_15_09_total1, half_15_09_total2, half_15_09_total3, half_15_09_total4, half_15_09_total5, half_15_09_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_15_09_hx6 : SourcePowerBound
    (powerBoxCross 9 9 64 half_15_09_φ6) (77590758807/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 9) (r := 2) (v := 0) (w := 12) (D := 64)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_15_09_φ6 (by norm_num [half_15_09_total1, half_15_09_total2, half_15_09_total3, half_15_09_total4, half_15_09_total5, half_15_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_15_09_total1, half_15_09_total2, half_15_09_total3, half_15_09_total4, half_15_09_total5, half_15_09_total6, parameterExponent, curveLoss, dyadicExponent]) half_15_09_hF2
    (admissibleExponent_zero 9) (half_12_09)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_09_total1, half_15_09_total2, half_15_09_total3, half_15_09_total4, half_15_09_total5, half_15_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_09_hx5 : SourcePowerBound
    (powerBoxCross 9 10 32 half_15_09_φ5) (277643293/31250000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 10) (u := 8) (t := 11)
    (D := 32) (ψ := (137223057/2500000000 : ℝ)) half_15_09_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_09_bounds5 l).1) (fun l => (half_15_09_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_09_total1, half_15_09_total2, half_15_09_total3, half_15_09_total4, half_15_09_total5, half_15_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_09)
    (by simpa only [half_15_09_φ6, show (2:ℝ)*32=64 by norm_num] using half_15_09_hx6)
  exact h.weaken (by norm_num [half_15_09_total1, half_15_09_total2, half_15_09_total3, half_15_09_total4, half_15_09_total5, half_15_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_09_hx4 : SourcePowerBound
    (powerBoxCross 9 11 16 half_15_09_φ4) (53020284903/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (76984933/1000000000 : ℝ)) half_15_09_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_09_bounds4 l).1) (fun l => (half_15_09_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_09_total1, half_15_09_total2, half_15_09_total3, half_15_09_total4, half_15_09_total5, half_15_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_09) (half_12_09)
    (by simpa only [half_15_09_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_09_hx5)
  exact h.weaken (by norm_num [half_15_09_total1, half_15_09_total2, half_15_09_total3, half_15_09_total4, half_15_09_total5, half_15_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_09_hx3 : SourcePowerBound
    (powerBoxCross 9 12 8 half_15_09_φ3) (128396068957/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (439913903/5000000000 : ℝ)) half_15_09_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_09_bounds3 l).1) (fun l => (half_15_09_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_09_total1, half_15_09_total2, half_15_09_total3, half_15_09_total4, half_15_09_total5, half_15_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_09) (half_13_09)
    (by simpa only [half_15_09_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_09_hx4)
  exact h.weaken (by norm_num [half_15_09_total1, half_15_09_total2, half_15_09_total3, half_15_09_total4, half_15_09_total5, half_15_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_09_hx2 : SourcePowerBound
    (powerBoxCross 9 13 4 half_15_09_φ2) (155814324047/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (950909431/10000000000 : ℝ)) half_15_09_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_09_bounds2 l).1) (fun l => (half_15_09_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_09_total1, half_15_09_total2, half_15_09_total3, half_15_09_total4, half_15_09_total5, half_15_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_09) (half_14_09)
    (by simpa only [half_15_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_09_hx3)
  exact h.weaken (by norm_num [half_15_09_total1, half_15_09_total2, half_15_09_total3, half_15_09_total4, half_15_09_total5, half_15_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_09_hx1 : SourcePowerBound
    (powerBoxCross 9 14 2 half_15_09_φ1) (187983548517/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (990442403/10000000000 : ℝ)) half_15_09_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_09_bounds1 l).1) (fun l => (half_15_09_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_09_total1, half_15_09_total2, half_15_09_total3, half_15_09_total4, half_15_09_total5, half_15_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_09) (half_15_08)
    (by simpa only [half_15_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_09_hx2)
  exact h.weaken (by norm_num [half_15_09_total1, half_15_09_total2, half_15_09_total3, half_15_09_total4, half_15_09_total5, half_15_09_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_15_09 : AdmissibleExponent 9 30 (215524242741/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 13) (ψ := (63751607/625000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_14_09)
    (by simpa only [half_15_09_φ1] using half_15_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_09_total1, half_15_09_total2, half_15_09_total3, half_15_09_total4, half_15_09_total5, half_15_09_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_16_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (51981323/500000000 : ℝ)

private theorem half_16_09_total1 : total half_16_09_φ1=(51981323/500000000 : ℝ) := by
  norm_num [half_16_09_φ1,total,emptyPhi,Fin.snoc]

private theorem half_16_09_bounds1 : ∀ l,0≤half_16_09_φ1 l ∧ half_16_09_φ1 l≤1 ∧
    0≤shiftExponents 9 half_16_09_φ1 l :=
  alternate_bounds_snoc emptyPhi (51981323/500000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_16_09_φ2 : Fin 2 → ℝ := Fin.snoc half_16_09_φ1 (506971363/5000000000 : ℝ)

private theorem half_16_09_total2 : total half_16_09_φ2=(1026784593/5000000000 : ℝ) := by
  change total (Fin.snoc half_16_09_φ1 (506971363/5000000000 : ℝ))=(1026784593/5000000000 : ℝ)
  rw [alternate_total_snoc,half_16_09_total1]
  norm_num

private theorem half_16_09_bounds2 : ∀ l,0≤half_16_09_φ2 l ∧ half_16_09_φ2 l≤1 ∧
    0≤shiftExponents 9 half_16_09_φ2 l :=
  alternate_bounds_snoc half_16_09_φ1 (506971363/5000000000 : ℝ) half_16_09_bounds1 (by norm_num)

private def half_16_09_φ3 : Fin 3 → ℝ := Fin.snoc half_16_09_φ2 (982957181/10000000000 : ℝ)

private theorem half_16_09_total3 : total half_16_09_φ3=(3036526367/10000000000 : ℝ) := by
  change total (Fin.snoc half_16_09_φ2 (982957181/10000000000 : ℝ))=(3036526367/10000000000 : ℝ)
  rw [alternate_total_snoc,half_16_09_total2]
  norm_num

private theorem half_16_09_bounds3 : ∀ l,0≤half_16_09_φ3 l ∧ half_16_09_φ3 l≤1 ∧
    0≤shiftExponents 9 half_16_09_φ3 l :=
  alternate_bounds_snoc half_16_09_φ2 (982957181/10000000000 : ℝ) half_16_09_bounds2 (by norm_num)

private def half_16_09_φ4 : Fin 4 → ℝ := Fin.snoc half_16_09_φ3 (870434203/10000000000 : ℝ)

private theorem half_16_09_total4 : total half_16_09_φ4=(390696057/1000000000 : ℝ) := by
  change total (Fin.snoc half_16_09_φ3 (870434203/10000000000 : ℝ))=(390696057/1000000000 : ℝ)
  rw [alternate_total_snoc,half_16_09_total3]
  norm_num

private theorem half_16_09_bounds4 : ∀ l,0≤half_16_09_φ4 l ∧ half_16_09_φ4 l≤1 ∧
    0≤shiftExponents 9 half_16_09_φ4 l :=
  alternate_bounds_snoc half_16_09_φ3 (870434203/10000000000 : ℝ) half_16_09_bounds3 (by norm_num)

private def half_16_09_φ5 : Fin 5 → ℝ := Fin.snoc half_16_09_φ4 (95203741/1250000000 : ℝ)

private theorem half_16_09_total5 : total half_16_09_φ5=(2334295249/5000000000 : ℝ) := by
  change total (Fin.snoc half_16_09_φ4 (95203741/1250000000 : ℝ))=(2334295249/5000000000 : ℝ)
  rw [alternate_total_snoc,half_16_09_total4]
  norm_num

private theorem half_16_09_bounds5 : ∀ l,0≤half_16_09_φ5 l ∧ half_16_09_φ5 l≤1 ∧
    0≤shiftExponents 9 half_16_09_φ5 l :=
  alternate_bounds_snoc half_16_09_φ4 (95203741/1250000000 : ℝ) half_16_09_bounds4 (by norm_num)

private def half_16_09_φ6 : Fin 6 → ℝ := Fin.snoc half_16_09_φ5 (13172321/200000000 : ℝ)

private theorem half_16_09_total6 : total half_16_09_φ6=(1331801637/2500000000 : ℝ) := by
  change total (Fin.snoc half_16_09_φ5 (13172321/200000000 : ℝ))=(1331801637/2500000000 : ℝ)
  rw [alternate_total_snoc,half_16_09_total5]
  norm_num

private theorem half_16_09_bounds6 : ∀ l,0≤half_16_09_φ6 l ∧ half_16_09_φ6 l≤1 ∧
    0≤shiftExponents 9 half_16_09_φ6 l :=
  alternate_bounds_snoc half_16_09_φ5 (13172321/200000000 : ℝ) half_16_09_bounds5 (by norm_num)

private theorem half_16_09_prefix : PrefixCondition 9 half_16_09_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_16_09_φ1, half_16_09_φ2, half_16_09_φ3, half_16_09_φ4, half_16_09_φ5, half_16_09_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_16_09_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_16_09_φ6) (2254595089/312500000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_16_09_φ6
    (fun i => (half_16_09_bounds6 i).1) (fun i => (half_16_09_bounds6 i).2.1)
    (fun i => (half_16_09_bounds6 i).2.2) half_16_09_prefix
  convert h using 1 <;> norm_num [half_16_09_total1, half_16_09_total2, half_16_09_total3, half_16_09_total4, half_16_09_total5, half_16_09_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_16_09_hx6 : SourcePowerBound
    (powerBoxCross 9 10 64 half_16_09_φ6) (20717743691/2500000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 10) (r := 2) (v := 13) (w := 14) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_16_09_φ6 (by norm_num [half_16_09_total1, half_16_09_total2, half_16_09_total3, half_16_09_total4, half_16_09_total5, half_16_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_16_09_total1, half_16_09_total2, half_16_09_total3, half_16_09_total4, half_16_09_total5, half_16_09_total6, parameterExponent, curveLoss, dyadicExponent]) half_16_09_hF2
    (half_13_09) (half_14_09)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_09_total1, half_16_09_total2, half_16_09_total3, half_16_09_total4, half_16_09_total5, half_16_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_09_hx5 : SourcePowerBound
    (powerBoxCross 9 11 32 half_16_09_φ5) (12126781489/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 11) (u := 9) (t := 12)
    (D := 32) (ψ := (13172321/200000000 : ℝ)) half_16_09_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_09_bounds5 l).1) (fun l => (half_16_09_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_09_total1, half_16_09_total2, half_16_09_total3, half_16_09_total4, half_16_09_total5, half_16_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_09) (half_12_09)
    (by simpa only [half_16_09_φ6, show (2:ℝ)*32=64 by norm_num] using half_16_09_hx6)
  exact h.weaken (by norm_num [half_16_09_total1, half_16_09_total2, half_16_09_total3, half_16_09_total4, half_16_09_total5, half_16_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_09_hx4 : SourcePowerBound
    (powerBoxCross 9 12 16 half_16_09_φ4) (57699110317/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (95203741/1250000000 : ℝ)) half_16_09_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_09_bounds4 l).1) (fun l => (half_16_09_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_09_total1, half_16_09_total2, half_16_09_total3, half_16_09_total4, half_16_09_total5, half_16_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_09) (half_13_09)
    (by simpa only [half_16_09_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_09_hx5)
  exact h.weaken (by norm_num [half_16_09_total1, half_16_09_total2, half_16_09_total3, half_16_09_total4, half_16_09_total5, half_16_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_09_hx3 : SourcePowerBound
    (powerBoxCross 9 13 8 half_16_09_φ3) (139175712737/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (870434203/10000000000 : ℝ)) half_16_09_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_09_bounds3 l).1) (fun l => (half_16_09_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_09_total1, half_16_09_total2, half_16_09_total3, half_16_09_total4, half_16_09_total5, half_16_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_09) (half_14_09)
    (by simpa only [half_16_09_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_09_hx4)
  exact h.weaken (by norm_num [half_16_09_total1, half_16_09_total2, half_16_09_total3, half_16_09_total4, half_16_09_total5, half_16_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_09_hx2 : SourcePowerBound
    (powerBoxCross 9 14 4 half_16_09_φ2) (42323242143/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (982957181/10000000000 : ℝ)) half_16_09_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_09_bounds2 l).1) (fun l => (half_16_09_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_09_total1, half_16_09_total2, half_16_09_total3, half_16_09_total4, half_16_09_total5, half_16_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_09) (half_15_09)
    (by simpa only [half_16_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_09_hx3)
  exact h.weaken (by norm_num [half_16_09_total1, half_16_09_total2, half_16_09_total3, half_16_09_total4, half_16_09_total5, half_16_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_09_hx1 : SourcePowerBound
    (powerBoxCross 9 15 2 half_16_09_φ1) (102078699327/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (506971363/5000000000 : ℝ)) half_16_09_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_09_bounds1 l).1) (fun l => (half_16_09_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_09_total1, half_16_09_total2, half_16_09_total3, half_16_09_total4, half_16_09_total5, half_16_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_09) (half_16_08)
    (by simpa only [half_16_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_09_hx2)
  exact h.weaken (by norm_num [half_16_09_total1, half_16_09_total2, half_16_09_total3, half_16_09_total4, half_16_09_total5, half_16_09_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_16_09 : AdmissibleExponent 9 32 (117153282997/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 14) (ψ := (51981323/500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_15_09)
    (by simpa only [half_16_09_φ1] using half_16_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_09_total1, half_16_09_total2, half_16_09_total3, half_16_09_total4, half_16_09_total5, half_16_09_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_17_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1056100641/10000000000 : ℝ)

private theorem half_17_09_total1 : total half_17_09_φ1=(1056100641/10000000000 : ℝ) := by
  norm_num [half_17_09_φ1,total,emptyPhi,Fin.snoc]

private theorem half_17_09_bounds1 : ∀ l,0≤half_17_09_φ1 l ∧ half_17_09_φ1 l≤1 ∧
    0≤shiftExponents 9 half_17_09_φ1 l :=
  alternate_bounds_snoc emptyPhi (1056100641/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_17_09_φ2 : Fin 2 → ℝ := Fin.snoc half_17_09_φ1 (1036110193/10000000000 : ℝ)

private theorem half_17_09_total2 : total half_17_09_φ2=(1046105417/5000000000 : ℝ) := by
  change total (Fin.snoc half_17_09_φ1 (1036110193/10000000000 : ℝ))=(1046105417/5000000000 : ℝ)
  rw [alternate_total_snoc,half_17_09_total1]
  norm_num

private theorem half_17_09_bounds2 : ∀ l,0≤half_17_09_φ2 l ∧ half_17_09_φ2 l≤1 ∧
    0≤shiftExponents 9 half_17_09_φ2 l :=
  alternate_bounds_snoc half_17_09_φ1 (1036110193/10000000000 : ℝ) half_17_09_bounds1 (by norm_num)

private def half_17_09_φ3 : Fin 3 → ℝ := Fin.snoc half_17_09_φ2 (197694729/2000000000 : ℝ)

private theorem half_17_09_total3 : total half_17_09_φ3=(3080684479/10000000000 : ℝ) := by
  change total (Fin.snoc half_17_09_φ2 (197694729/2000000000 : ℝ))=(3080684479/10000000000 : ℝ)
  rw [alternate_total_snoc,half_17_09_total2]
  norm_num

private theorem half_17_09_bounds3 : ∀ l,0≤half_17_09_φ3 l ∧ half_17_09_φ3 l≤1 ∧
    0≤shiftExponents 9 half_17_09_φ3 l :=
  alternate_bounds_snoc half_17_09_φ2 (197694729/2000000000 : ℝ) half_17_09_bounds2 (by norm_num)

private def half_17_09_φ4 : Fin 4 → ℝ := Fin.snoc half_17_09_φ3 (864914439/10000000000 : ℝ)

private theorem half_17_09_total4 : total half_17_09_φ4=(1972799459/5000000000 : ℝ) := by
  change total (Fin.snoc half_17_09_φ3 (864914439/10000000000 : ℝ))=(1972799459/5000000000 : ℝ)
  rw [alternate_total_snoc,half_17_09_total3]
  norm_num

private theorem half_17_09_bounds4 : ∀ l,0≤half_17_09_φ4 l ∧ half_17_09_φ4 l≤1 ∧
    0≤shiftExponents 9 half_17_09_φ4 l :=
  alternate_bounds_snoc half_17_09_φ3 (864914439/10000000000 : ℝ) half_17_09_bounds3 (by norm_num)

private def half_17_09_φ5 : Fin 5 → ℝ := Fin.snoc half_17_09_φ4 (378400067/5000000000 : ℝ)

private theorem half_17_09_total5 : total half_17_09_φ5=(1175599763/2500000000 : ℝ) := by
  change total (Fin.snoc half_17_09_φ4 (378400067/5000000000 : ℝ))=(1175599763/2500000000 : ℝ)
  rw [alternate_total_snoc,half_17_09_total4]
  norm_num

private theorem half_17_09_bounds5 : ∀ l,0≤half_17_09_φ5 l ∧ half_17_09_φ5 l≤1 ∧
    0≤shiftExponents 9 half_17_09_φ5 l :=
  alternate_bounds_snoc half_17_09_φ4 (378400067/5000000000 : ℝ) half_17_09_bounds4 (by norm_num)

private def half_17_09_φ6 : Fin 6 → ℝ := Fin.snoc half_17_09_φ5 (331100059/5000000000 : ℝ)

private theorem half_17_09_total6 : total half_17_09_φ6=(536459917/1000000000 : ℝ) := by
  change total (Fin.snoc half_17_09_φ5 (331100059/5000000000 : ℝ))=(536459917/1000000000 : ℝ)
  rw [alternate_total_snoc,half_17_09_total5]
  norm_num

private theorem half_17_09_bounds6 : ∀ l,0≤half_17_09_φ6 l ∧ half_17_09_φ6 l≤1 ∧
    0≤shiftExponents 9 half_17_09_φ6 l :=
  alternate_bounds_snoc half_17_09_φ5 (331100059/5000000000 : ℝ) half_17_09_bounds5 (by norm_num)

private theorem half_17_09_prefix : PrefixCondition 9 half_17_09_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_17_09_φ1, half_17_09_φ2, half_17_09_φ3, half_17_09_φ4, half_17_09_φ5, half_17_09_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_17_09_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_17_09_φ6) (890620249/125000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_17_09_φ6
    (fun i => (half_17_09_bounds6 i).1) (fun i => (half_17_09_bounds6 i).2.1)
    (fun i => (half_17_09_bounds6 i).2.2) half_17_09_prefix
  convert h using 1 <;> norm_num [half_17_09_total1, half_17_09_total2, half_17_09_total3, half_17_09_total4, half_17_09_total5, half_17_09_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_17_09_hx6 : SourcePowerBound
    (powerBoxCross 9 11 64 half_17_09_φ6) (90601305337/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 11) (r := 2) (v := 14) (w := 15) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_17_09_φ6 (by norm_num [half_17_09_total1, half_17_09_total2, half_17_09_total3, half_17_09_total4, half_17_09_total5, half_17_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_17_09_total1, half_17_09_total2, half_17_09_total3, half_17_09_total4, half_17_09_total5, half_17_09_total6, parameterExponent, curveLoss, dyadicExponent]) half_17_09_hF2
    (half_14_09) (half_15_09)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_09_total1, half_17_09_total2, half_17_09_total3, half_17_09_total4, half_17_09_total5, half_17_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_09_hx5 : SourcePowerBound
    (powerBoxCross 9 12 32 half_17_09_φ5) (105848226393/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 12) (u := 10) (t := 13)
    (D := 32) (ψ := (331100059/5000000000 : ℝ)) half_17_09_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_09_bounds5 l).1) (fun l => (half_17_09_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_09_total1, half_17_09_total2, half_17_09_total3, half_17_09_total4, half_17_09_total5, half_17_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_09) (half_13_09)
    (by simpa only [half_17_09_φ6, show (2:ℝ)*32=64 by norm_num] using half_17_09_hx6)
  exact h.weaken (by norm_num [half_17_09_total1, half_17_09_total2, half_17_09_total3, half_17_09_total4, half_17_09_total5, half_17_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_09_hx4 : SourcePowerBound
    (powerBoxCross 9 13 16 half_17_09_φ4) (125500331741/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (378400067/5000000000 : ℝ)) half_17_09_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_09_bounds4 l).1) (fun l => (half_17_09_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_09_total1, half_17_09_total2, half_17_09_total3, half_17_09_total4, half_17_09_total5, half_17_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_09) (half_14_09)
    (by simpa only [half_17_09_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_09_hx5)
  exact h.weaken (by norm_num [half_17_09_total1, half_17_09_total2, half_17_09_total3, half_17_09_total4, half_17_09_total5, half_17_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_09_hx3 : SourcePowerBound
    (powerBoxCross 9 14 8 half_17_09_φ3) (7540143517/500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (864914439/10000000000 : ℝ)) half_17_09_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_09_bounds3 l).1) (fun l => (half_17_09_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_09_total1, half_17_09_total2, half_17_09_total3, half_17_09_total4, half_17_09_total5, half_17_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_09) (half_15_09)
    (by simpa only [half_17_09_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_09_hx4)
  exact h.weaken (by norm_num [half_17_09_total1, half_17_09_total2, half_17_09_total3, half_17_09_total4, half_17_09_total5, half_17_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_09_hx2 : SourcePowerBound
    (powerBoxCross 9 15 4 half_17_09_φ2) (183019332247/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (197694729/2000000000 : ℝ)) half_17_09_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_09_bounds2 l).1) (fun l => (half_17_09_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_09_total1, half_17_09_total2, half_17_09_total3, half_17_09_total4, half_17_09_total5, half_17_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_09) (half_16_09)
    (by simpa only [half_17_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_09_hx3)
  exact h.weaken (by norm_num [half_17_09_total1, half_17_09_total2, half_17_09_total3, half_17_09_total4, half_17_09_total5, half_17_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_09_hx1 : SourcePowerBound
    (powerBoxCross 9 16 2 half_17_09_φ1) (220617535183/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (1036110193/10000000000 : ℝ)) half_17_09_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_09_bounds1 l).1) (fun l => (half_17_09_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_09_total1, half_17_09_total2, half_17_09_total3, half_17_09_total4, half_17_09_total5, half_17_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_09) (half_17_08)
    (by simpa only [half_17_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_09_hx2)
  exact h.weaken (by norm_num [half_17_09_total1, half_17_09_total2, half_17_09_total3, half_17_09_total4, half_17_09_total5, half_17_09_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_17_09 : AdmissibleExponent 9 34 (126678327527/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 15) (ψ := (1056100641/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_16_09)
    (by simpa only [half_17_09_φ1] using half_17_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_09_total1, half_17_09_total2, half_17_09_total3, half_17_09_total4, half_17_09_total5, half_17_09_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_18_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (267244193/2500000000 : ℝ)

private theorem half_18_09_total1 : total half_18_09_φ1=(267244193/2500000000 : ℝ) := by
  norm_num [half_18_09_φ1,total,emptyPhi,Fin.snoc]

private theorem half_18_09_bounds1 : ∀ l,0≤half_18_09_φ1 l ∧ half_18_09_φ1 l≤1 ∧
    0≤shiftExponents 9 half_18_09_φ1 l :=
  alternate_bounds_snoc emptyPhi (267244193/2500000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_18_09_φ2 : Fin 2 → ℝ := Fin.snoc half_18_09_φ1 (210813417/2000000000 : ℝ)

private theorem half_18_09_total2 : total half_18_09_φ2=(2123043857/10000000000 : ℝ) := by
  change total (Fin.snoc half_18_09_φ1 (210813417/2000000000 : ℝ))=(2123043857/10000000000 : ℝ)
  rw [alternate_total_snoc,half_18_09_total1]
  norm_num

private theorem half_18_09_bounds2 : ∀ l,0≤half_18_09_φ2 l ∧ half_18_09_φ2 l≤1 ∧
    0≤shiftExponents 9 half_18_09_φ2 l :=
  alternate_bounds_snoc half_18_09_φ1 (210813417/2000000000 : ℝ) half_18_09_bounds1 (by norm_num)

private def half_18_09_φ3 : Fin 3 → ℝ := Fin.snoc half_18_09_φ2 (984619517/10000000000 : ℝ)

private theorem half_18_09_total3 : total half_18_09_φ3=(1553831687/5000000000 : ℝ) := by
  change total (Fin.snoc half_18_09_φ2 (984619517/10000000000 : ℝ))=(1553831687/5000000000 : ℝ)
  rw [alternate_total_snoc,half_18_09_total2]
  norm_num

private theorem half_18_09_bounds3 : ∀ l,0≤half_18_09_φ3 l ∧ half_18_09_φ3 l≤1 ∧
    0≤shiftExponents 9 half_18_09_φ3 l :=
  alternate_bounds_snoc half_18_09_φ2 (984619517/10000000000 : ℝ) half_18_09_bounds2 (by norm_num)

private def half_18_09_φ4 : Fin 4 → ℝ := Fin.snoc half_18_09_φ3 (430771039/5000000000 : ℝ)

private theorem half_18_09_total4 : total half_18_09_φ4=(992301363/2500000000 : ℝ) := by
  change total (Fin.snoc half_18_09_φ3 (430771039/5000000000 : ℝ))=(992301363/2500000000 : ℝ)
  rw [alternate_total_snoc,half_18_09_total3]
  norm_num

private theorem half_18_09_bounds4 : ∀ l,0≤half_18_09_φ4 l ∧ half_18_09_φ4 l≤1 ∧
    0≤shiftExponents 9 half_18_09_φ4 l :=
  alternate_bounds_snoc half_18_09_φ3 (430771039/5000000000 : ℝ) half_18_09_bounds3 (by norm_num)

private def half_18_09_φ5 : Fin 5 → ℝ := Fin.snoc half_18_09_φ4 (376924659/5000000000 : ℝ)

private theorem half_18_09_total5 : total half_18_09_φ5=(472305477/1000000000 : ℝ) := by
  change total (Fin.snoc half_18_09_φ4 (376924659/5000000000 : ℝ))=(472305477/1000000000 : ℝ)
  rw [alternate_total_snoc,half_18_09_total4]
  norm_num

private theorem half_18_09_bounds5 : ∀ l,0≤half_18_09_φ5 l ∧ half_18_09_φ5 l≤1 ∧
    0≤shiftExponents 9 half_18_09_φ5 l :=
  alternate_bounds_snoc half_18_09_φ4 (376924659/5000000000 : ℝ) half_18_09_bounds4 (by norm_num)

private def half_18_09_φ6 : Fin 6 → ℝ := Fin.snoc half_18_09_φ5 (659618153/10000000000 : ℝ)

private theorem half_18_09_total6 : total half_18_09_φ6=(5382672923/10000000000 : ℝ) := by
  change total (Fin.snoc half_18_09_φ5 (659618153/10000000000 : ℝ))=(5382672923/10000000000 : ℝ)
  rw [alternate_total_snoc,half_18_09_total5]
  norm_num

private theorem half_18_09_bounds6 : ∀ l,0≤half_18_09_φ6 l ∧ half_18_09_φ6 l≤1 ∧
    0≤shiftExponents 9 half_18_09_φ6 l :=
  alternate_bounds_snoc half_18_09_φ5 (659618153/10000000000 : ℝ) half_18_09_bounds5 (by norm_num)

private theorem half_18_09_prefix : PrefixCondition 9 half_18_09_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_18_09_φ1, half_18_09_φ2, half_18_09_φ3, half_18_09_φ4, half_18_09_φ5, half_18_09_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_18_09_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_18_09_φ6) (8851981231/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_18_09_φ6
    (fun i => (half_18_09_bounds6 i).1) (fun i => (half_18_09_bounds6 i).2.1)
    (fun i => (half_18_09_bounds6 i).2.2) half_18_09_prefix
  convert h using 1 <;> norm_num [half_18_09_total1, half_18_09_total2, half_18_09_total3, half_18_09_total4, half_18_09_total5, half_18_09_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_18_09_hx6 : SourcePowerBound
    (powerBoxCross 9 12 64 half_18_09_φ6) (24711054081/2500000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 12) (r := 2) (v := 0) (w := 16) (D := 64)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_18_09_φ6 (by norm_num [half_18_09_total1, half_18_09_total2, half_18_09_total3, half_18_09_total4, half_18_09_total5, half_18_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_18_09_total1, half_18_09_total2, half_18_09_total3, half_18_09_total4, half_18_09_total5, half_18_09_total6, parameterExponent, curveLoss, dyadicExponent]) half_18_09_hF2
    (admissibleExponent_zero 9) (half_16_09)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_18_09_total1, half_18_09_total2, half_18_09_total3, half_18_09_total4, half_18_09_total5, half_18_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_09_hx5 : SourcePowerBound
    (powerBoxCross 9 13 32 half_18_09_φ5) (115110458383/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 13) (u := 11) (t := 14)
    (D := 32) (ψ := (659618153/10000000000 : ℝ)) half_18_09_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_09_bounds5 l).1) (fun l => (half_18_09_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_09_total1, half_18_09_total2, half_18_09_total3, half_18_09_total4, half_18_09_total5, half_18_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_09) (half_14_09)
    (by simpa only [half_18_09_φ6, show (2:ℝ)*32=64 by norm_num] using half_18_09_hx6)
  exact h.weaken (by norm_num [half_18_09_total1, half_18_09_total2, half_18_09_total3, half_18_09_total4, half_18_09_total5, half_18_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_09_hx4 : SourcePowerBound
    (powerBoxCross 9 14 16 half_18_09_φ4) (136090645263/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 14) (u := 12) (t := 15)
    (D := 16) (ψ := (376924659/5000000000 : ℝ)) half_18_09_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_09_bounds4 l).1) (fun l => (half_18_09_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_09_total1, half_18_09_total2, half_18_09_total3, half_18_09_total4, half_18_09_total5, half_18_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_09) (half_15_09)
    (by simpa only [half_18_09_φ5, show (2:ℝ)*16=32 by norm_num] using half_18_09_hx5)
  exact h.weaken (by norm_num [half_18_09_total1, half_18_09_total2, half_18_09_total3, half_18_09_total4, half_18_09_total5, half_18_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_09_hx3 : SourcePowerBound
    (powerBoxCross 9 15 8 half_18_09_φ3) (32598294703/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 15) (u := 13) (t := 16)
    (D := 8) (ψ := (430771039/5000000000 : ℝ)) half_18_09_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_09_bounds3 l).1) (fun l => (half_18_09_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_09_total1, half_18_09_total2, half_18_09_total3, half_18_09_total4, half_18_09_total5, half_18_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_09) (half_16_09)
    (by simpa only [half_18_09_φ4, show (2:ℝ)*8=16 by norm_num] using half_18_09_hx4)
  exact h.weaken (by norm_num [half_18_09_total1, half_18_09_total2, half_18_09_total3, half_18_09_total4, half_18_09_total5, half_18_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_09_hx2 : SourcePowerBound
    (powerBoxCross 9 16 4 half_18_09_φ2) (98532253673/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 16) (u := 14) (t := 17)
    (D := 4) (ψ := (984619517/10000000000 : ℝ)) half_18_09_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_09_bounds2 l).1) (fun l => (half_18_09_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_09_total1, half_18_09_total2, half_18_09_total3, half_18_09_total4, half_18_09_total5, half_18_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_09) (half_17_09)
    (by simpa only [half_18_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_18_09_hx3)
  exact h.weaken (by norm_num [half_18_09_total1, half_18_09_total2, half_18_09_total3, half_18_09_total4, half_18_09_total5, half_18_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_09_hx1 : SourcePowerBound
    (powerBoxCross 9 17 2 half_18_09_φ1) (237342393907/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 17) (u := 15) (t := 18)
    (D := 2) (ψ := (210813417/2000000000 : ℝ)) half_18_09_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_09_bounds1 l).1) (fun l => (half_18_09_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_09_total1, half_18_09_total2, half_18_09_total3, half_18_09_total4, half_18_09_total5, half_18_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_09) (half_18_08)
    (by simpa only [half_18_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_18_09_hx2)
  exact h.weaken (by norm_num [half_18_09_total1, half_18_09_total2, half_18_09_total3, half_18_09_total4, half_18_09_total5, half_18_09_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_18_09 : AdmissibleExponent 9 36 (272618627383/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 16) (ψ := (267244193/2500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_17_09)
    (by simpa only [half_18_09_φ1] using half_18_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_18_09_total1, half_18_09_total2, half_18_09_total3, half_18_09_total4, half_18_09_total5, half_18_09_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_19_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (269803101/2500000000 : ℝ)

private theorem half_19_09_total1 : total half_19_09_φ1=(269803101/2500000000 : ℝ) := by
  norm_num [half_19_09_φ1,total,emptyPhi,Fin.snoc]

private theorem half_19_09_bounds1 : ∀ l,0≤half_19_09_φ1 l ∧ half_19_09_φ1 l≤1 ∧
    0≤shiftExponents 9 half_19_09_φ1 l :=
  alternate_bounds_snoc emptyPhi (269803101/2500000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_19_09_φ2 : Fin 2 → ℝ := Fin.snoc half_19_09_φ1 (53406731/500000000 : ℝ)

private theorem half_19_09_total2 : total half_19_09_φ2=(134209189/625000000 : ℝ) := by
  change total (Fin.snoc half_19_09_φ1 (53406731/500000000 : ℝ))=(134209189/625000000 : ℝ)
  rw [alternate_total_snoc,half_19_09_total1]
  norm_num

private theorem half_19_09_bounds2 : ∀ l,0≤half_19_09_φ2 l ∧ half_19_09_φ2 l≤1 ∧
    0≤shiftExponents 9 half_19_09_φ2 l :=
  alternate_bounds_snoc half_19_09_φ1 (53406731/500000000 : ℝ) half_19_09_bounds1 (by norm_num)

private def half_19_09_φ3 : Fin 3 → ℝ := Fin.snoc half_19_09_φ2 (981581621/10000000000 : ℝ)

private theorem half_19_09_total3 : total half_19_09_φ3=(625785729/2000000000 : ℝ) := by
  change total (Fin.snoc half_19_09_φ2 (981581621/10000000000 : ℝ))=(625785729/2000000000 : ℝ)
  rw [alternate_total_snoc,half_19_09_total2]
  norm_num

private theorem half_19_09_bounds3 : ∀ l,0≤half_19_09_φ3 l ∧ half_19_09_φ3 l≤1 ∧
    0≤shiftExponents 9 half_19_09_φ3 l :=
  alternate_bounds_snoc half_19_09_φ2 (981581621/10000000000 : ℝ) half_19_09_bounds2 (by norm_num)

private def half_19_09_φ4 : Fin 4 → ℝ := Fin.snoc half_19_09_φ3 (858883919/10000000000 : ℝ)

private theorem half_19_09_total4 : total half_19_09_φ4=(996953141/2500000000 : ℝ) := by
  change total (Fin.snoc half_19_09_φ3 (858883919/10000000000 : ℝ))=(996953141/2500000000 : ℝ)
  rw [alternate_total_snoc,half_19_09_total3]
  norm_num

private theorem half_19_09_bounds4 : ∀ l,0≤half_19_09_φ4 l ∧ half_19_09_φ4 l≤1 ∧
    0≤shiftExponents 9 half_19_09_φ4 l :=
  alternate_bounds_snoc half_19_09_φ3 (858883919/10000000000 : ℝ) half_19_09_bounds3 (by norm_num)

private def half_19_09_φ5 : Fin 5 → ℝ := Fin.snoc half_19_09_φ4 (751523429/10000000000 : ℝ)

private theorem half_19_09_total5 : total half_19_09_φ5=(4739335993/10000000000 : ℝ) := by
  change total (Fin.snoc half_19_09_φ4 (751523429/10000000000 : ℝ))=(4739335993/10000000000 : ℝ)
  rw [alternate_total_snoc,half_19_09_total4]
  norm_num

private theorem half_19_09_bounds5 : ∀ l,0≤half_19_09_φ5 l ∧ half_19_09_φ5 l≤1 ∧
    0≤shiftExponents 9 half_19_09_φ5 l :=
  alternate_bounds_snoc half_19_09_φ4 (751523429/10000000000 : ℝ) half_19_09_bounds4 (by norm_num)

private def half_19_09_φ6 : Fin 6 → ℝ := Fin.snoc half_19_09_φ5 (657583/10000000 : ℝ)

private theorem half_19_09_total6 : total half_19_09_φ6=(5396918993/10000000000 : ℝ) := by
  change total (Fin.snoc half_19_09_φ5 (657583/10000000 : ℝ))=(5396918993/10000000000 : ℝ)
  rw [alternate_total_snoc,half_19_09_total5]
  norm_num

private theorem half_19_09_bounds6 : ∀ l,0≤half_19_09_φ6 l ∧ half_19_09_φ6 l≤1 ∧
    0≤shiftExponents 9 half_19_09_φ6 l :=
  alternate_bounds_snoc half_19_09_φ5 (657583/10000000 : ℝ) half_19_09_bounds5 (by norm_num)

private theorem half_19_09_prefix : PrefixCondition 9 half_19_09_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_19_09_φ1, half_19_09_φ2, half_19_09_φ3, half_19_09_φ4, half_19_09_φ5, half_19_09_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_19_09_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_19_09_φ6) (8809243021/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_19_09_φ6
    (fun i => (half_19_09_bounds6 i).1) (fun i => (half_19_09_bounds6 i).2.1)
    (fun i => (half_19_09_bounds6 i).2.2) half_19_09_prefix
  convert h using 1 <;> norm_num [half_19_09_total1, half_19_09_total2, half_19_09_total3, half_19_09_total4, half_19_09_total5, half_19_09_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_19_09_hx6 : SourcePowerBound
    (powerBoxCross 9 13 64 half_19_09_φ6) (107301687033/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 13) (r := 2) (v := 17) (w := 18) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_19_09_φ6 (by norm_num [half_19_09_total1, half_19_09_total2, half_19_09_total3, half_19_09_total4, half_19_09_total5, half_19_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_19_09_total1, half_19_09_total2, half_19_09_total3, half_19_09_total4, half_19_09_total5, half_19_09_total6, parameterExponent, curveLoss, dyadicExponent]) half_19_09_hF2
    (half_17_09) (half_18_09)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_19_09_total1, half_19_09_total2, half_19_09_total3, half_19_09_total4, half_19_09_total5, half_19_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_09_hx5 : SourcePowerBound
    (powerBoxCross 9 14 32 half_19_09_φ5) (62301659183/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 14) (u := 12) (t := 15)
    (D := 32) (ψ := (657583/10000000 : ℝ)) half_19_09_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_09_bounds5 l).1) (fun l => (half_19_09_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_09_total1, half_19_09_total2, half_19_09_total3, half_19_09_total4, half_19_09_total5, half_19_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_09) (half_15_09)
    (by simpa only [half_19_09_φ6, show (2:ℝ)*32=64 by norm_num] using half_19_09_hx6)
  exact h.weaken (by norm_num [half_19_09_total1, half_19_09_total2, half_19_09_total3, half_19_09_total4, half_19_09_total5, half_19_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_09_hx4 : SourcePowerBound
    (powerBoxCross 9 15 16 half_19_09_φ4) (146930724831/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 15) (u := 13) (t := 16)
    (D := 16) (ψ := (751523429/10000000000 : ℝ)) half_19_09_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_09_bounds4 l).1) (fun l => (half_19_09_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_09_total1, half_19_09_total2, half_19_09_total3, half_19_09_total4, half_19_09_total5, half_19_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_09) (half_16_09)
    (by simpa only [half_19_09_φ5, show (2:ℝ)*16=32 by norm_num] using half_19_09_hx5)
  exact h.weaken (by norm_num [half_19_09_total1, half_19_09_total2, half_19_09_total3, half_19_09_total4, half_19_09_total5, half_19_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_09_hx3 : SourcePowerBound
    (powerBoxCross 9 16 8 half_19_09_φ3) (175445047419/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 16) (u := 14) (t := 17)
    (D := 8) (ψ := (858883919/10000000000 : ℝ)) half_19_09_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_09_bounds3 l).1) (fun l => (half_19_09_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_09_total1, half_19_09_total2, half_19_09_total3, half_19_09_total4, half_19_09_total5, half_19_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_09) (half_17_09)
    (by simpa only [half_19_09_φ4, show (2:ℝ)*8=16 by norm_num] using half_19_09_hx4)
  exact h.weaken (by norm_num [half_19_09_total1, half_19_09_total2, half_19_09_total3, half_19_09_total4, half_19_09_total5, half_19_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_09_hx2 : SourcePowerBound
    (powerBoxCross 9 17 4 half_19_09_φ2) (211386624521/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 17) (u := 15) (t := 18)
    (D := 4) (ψ := (981581621/10000000000 : ℝ)) half_19_09_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_09_bounds2 l).1) (fun l => (half_19_09_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_09_total1, half_19_09_total2, half_19_09_total3, half_19_09_total4, half_19_09_total5, half_19_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_09) (half_18_09)
    (by simpa only [half_19_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_19_09_hx3)
  exact h.weaken (by norm_num [half_19_09_total1, half_19_09_total2, half_19_09_total3, half_19_09_total4, half_19_09_total5, half_19_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_09_hx1 : SourcePowerBound
    (powerBoxCross 9 18 2 half_19_09_φ1) (254276499369/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 18) (u := 16) (t := 19)
    (D := 2) (ψ := (53406731/500000000 : ℝ)) half_19_09_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_09_bounds1 l).1) (fun l => (half_19_09_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_09_total1, half_19_09_total2, half_19_09_total3, half_19_09_total4, half_19_09_total5, half_19_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_09) (half_19_08)
    (by simpa only [half_19_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_19_09_hx2)
  exact h.weaken (by norm_num [half_19_09_total1, half_19_09_total2, half_19_09_total3, half_19_09_total4, half_19_09_total5, half_19_09_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_19_09 : AdmissibleExponent 9 38 (292048933509/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 17) (ψ := (269803101/2500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_18_09)
    (by simpa only [half_19_09_φ1] using half_19_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_19_09_total1, half_19_09_total2, half_19_09_total3, half_19_09_total4, half_19_09_total5, half_19_09_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_20_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1087187623/10000000000 : ℝ)

private theorem half_20_09_total1 : total half_20_09_φ1=(1087187623/10000000000 : ℝ) := by
  norm_num [half_20_09_φ1,total,emptyPhi,Fin.snoc]

private theorem half_20_09_bounds1 : ∀ l,0≤half_20_09_φ1 l ∧ half_20_09_φ1 l≤1 ∧
    0≤shiftExponents 9 half_20_09_φ1 l :=
  alternate_bounds_snoc emptyPhi (1087187623/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_20_09_φ2 : Fin 2 → ℝ := Fin.snoc half_20_09_φ1 (539598077/5000000000 : ℝ)

private theorem half_20_09_total2 : total half_20_09_φ2=(2166383777/10000000000 : ℝ) := by
  change total (Fin.snoc half_20_09_φ1 (539598077/5000000000 : ℝ))=(2166383777/10000000000 : ℝ)
  rw [alternate_total_snoc,half_20_09_total1]
  norm_num

private theorem half_20_09_bounds2 : ∀ l,0≤half_20_09_φ2 l ∧ half_20_09_φ2 l≤1 ∧
    0≤shiftExponents 9 half_20_09_φ2 l :=
  alternate_bounds_snoc half_20_09_φ1 (539598077/5000000000 : ℝ) half_20_09_bounds1 (by norm_num)

private def half_20_09_φ3 : Fin 3 → ℝ := Fin.snoc half_20_09_φ2 (979202027/10000000000 : ℝ)

private theorem half_20_09_total3 : total half_20_09_φ3=(786396451/2500000000 : ℝ) := by
  change total (Fin.snoc half_20_09_φ2 (979202027/10000000000 : ℝ))=(786396451/2500000000 : ℝ)
  rw [alternate_total_snoc,half_20_09_total2]
  norm_num

private theorem half_20_09_bounds3 : ∀ l,0≤half_20_09_φ3 l ∧ half_20_09_φ3 l≤1 ∧
    0≤shiftExponents 9 half_20_09_φ3 l :=
  alternate_bounds_snoc half_20_09_φ2 (979202027/10000000000 : ℝ) half_20_09_bounds2 (by norm_num)

private def half_20_09_φ4 : Fin 4 → ℝ := Fin.snoc half_20_09_φ3 (428400887/5000000000 : ℝ)

private theorem half_20_09_total4 : total half_20_09_φ4=(2001193789/5000000000 : ℝ) := by
  change total (Fin.snoc half_20_09_φ3 (428400887/5000000000 : ℝ))=(2001193789/5000000000 : ℝ)
  rw [alternate_total_snoc,half_20_09_total3]
  norm_num

private theorem half_20_09_bounds4 : ∀ l,0≤half_20_09_φ4 l ∧ half_20_09_φ4 l≤1 ∧
    0≤shiftExponents 9 half_20_09_φ4 l :=
  alternate_bounds_snoc half_20_09_φ3 (428400887/5000000000 : ℝ) half_20_09_bounds3 (by norm_num)

private def half_20_09_φ5 : Fin 5 → ℝ := Fin.snoc half_20_09_φ4 (46856347/625000000 : ℝ)

private theorem half_20_09_total5 : total half_20_09_φ5=(475208913/1000000000 : ℝ) := by
  change total (Fin.snoc half_20_09_φ4 (46856347/625000000 : ℝ))=(475208913/1000000000 : ℝ)
  rw [alternate_total_snoc,half_20_09_total4]
  norm_num

private theorem half_20_09_bounds5 : ∀ l,0≤half_20_09_φ5 l ∧ half_20_09_φ5 l≤1 ∧
    0≤shiftExponents 9 half_20_09_φ5 l :=
  alternate_bounds_snoc half_20_09_φ4 (46856347/625000000 : ℝ) half_20_09_bounds4 (by norm_num)

private def half_20_09_φ6 : Fin 6 → ℝ := Fin.snoc half_20_09_φ5 (327994429/5000000000 : ℝ)

private theorem half_20_09_total6 : total half_20_09_φ6=(1352019497/2500000000 : ℝ) := by
  change total (Fin.snoc half_20_09_φ5 (327994429/5000000000 : ℝ))=(1352019497/2500000000 : ℝ)
  rw [alternate_total_snoc,half_20_09_total5]
  norm_num

private theorem half_20_09_bounds6 : ∀ l,0≤half_20_09_φ6 l ∧ half_20_09_φ6 l≤1 ∧
    0≤shiftExponents 9 half_20_09_φ6 l :=
  alternate_bounds_snoc half_20_09_φ5 (327994429/5000000000 : ℝ) half_20_09_bounds5 (by norm_num)

private theorem half_20_09_prefix : PrefixCondition 9 half_20_09_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_20_09_φ1, half_20_09_φ2, half_20_09_φ3, half_20_09_φ4, half_20_09_φ5, half_20_09_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_20_09_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_20_09_φ6) (2193941509/312500000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_20_09_φ6
    (fun i => (half_20_09_bounds6 i).1) (fun i => (half_20_09_bounds6 i).2.1)
    (fun i => (half_20_09_bounds6 i).2.2) half_20_09_prefix
  convert h using 1 <;> norm_num [half_20_09_total1, half_20_09_total2, half_20_09_total3, half_20_09_total4, half_20_09_total5, half_20_09_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_20_09_hx6 : SourcePowerBound
    (powerBoxCross 9 14 64 half_20_09_φ6) (11590091529/1000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 14) (r := 2) (v := 18) (w := 19) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_20_09_φ6 (by norm_num [half_20_09_total1, half_20_09_total2, half_20_09_total3, half_20_09_total4, half_20_09_total5, half_20_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_20_09_total1, half_20_09_total2, half_20_09_total3, half_20_09_total4, half_20_09_total5, half_20_09_total6, parameterExponent, curveLoss, dyadicExponent]) half_20_09_hF2
    (half_18_09) (half_19_09)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_20_09_total1, half_20_09_total2, half_20_09_total3, half_20_09_total4, half_20_09_total5, half_20_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_09_hx5 : SourcePowerBound
    (powerBoxCross 9 15 32 half_20_09_φ5) (67139474719/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 15) (u := 13) (t := 16)
    (D := 32) (ψ := (327994429/5000000000 : ℝ)) half_20_09_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_09_bounds5 l).1) (fun l => (half_20_09_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_09_total1, half_20_09_total2, half_20_09_total3, half_20_09_total4, half_20_09_total5, half_20_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_09) (half_16_09)
    (by simpa only [half_20_09_φ6, show (2:ℝ)*32=64 by norm_num] using half_20_09_hx6)
  exact h.weaken (by norm_num [half_20_09_total1, half_20_09_total2, half_20_09_total3, half_20_09_total4, half_20_09_total5, half_20_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_09_hx4 : SourcePowerBound
    (powerBoxCross 9 16 16 half_20_09_φ4) (157977347989/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 16) (u := 14) (t := 17)
    (D := 16) (ψ := (46856347/625000000 : ℝ)) half_20_09_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_09_bounds4 l).1) (fun l => (half_20_09_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_09_total1, half_20_09_total2, half_20_09_total3, half_20_09_total4, half_20_09_total5, half_20_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_09) (half_17_09)
    (by simpa only [half_20_09_φ5, show (2:ℝ)*16=32 by norm_num] using half_20_09_hx5)
  exact h.weaken (by norm_num [half_20_09_total1, half_20_09_total2, half_20_09_total3, half_20_09_total4, half_20_09_total5, half_20_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_09_hx3 : SourcePowerBound
    (powerBoxCross 9 17 8 half_20_09_φ3) (188118807757/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 17) (u := 15) (t := 18)
    (D := 8) (ψ := (428400887/5000000000 : ℝ)) half_20_09_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_09_bounds3 l).1) (fun l => (half_20_09_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_09_total1, half_20_09_total2, half_20_09_total3, half_20_09_total4, half_20_09_total5, half_20_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_09) (half_18_09)
    (by simpa only [half_20_09_φ4, show (2:ℝ)*8=16 by norm_num] using half_20_09_hx4)
  exact h.weaken (by norm_num [half_20_09_total1, half_20_09_total2, half_20_09_total3, half_20_09_total4, half_20_09_total5, half_20_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_09_hx2 : SourcePowerBound
    (powerBoxCross 9 18 4 half_20_09_φ2) (225940665389/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 18) (u := 16) (t := 19)
    (D := 4) (ψ := (979202027/10000000000 : ℝ)) half_20_09_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_09_bounds2 l).1) (fun l => (half_20_09_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_09_total1, half_20_09_total2, half_20_09_total3, half_20_09_total4, half_20_09_total5, half_20_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_09) (half_19_09)
    (by simpa only [half_20_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_20_09_hx3)
  exact h.weaken (by norm_num [half_20_09_total1, half_20_09_total2, half_20_09_total3, half_20_09_total4, half_20_09_total5, half_20_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_09_hx1 : SourcePowerBound
    (powerBoxCross 9 19 2 half_20_09_φ1) (33923115319/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 19) (u := 17) (t := 20)
    (D := 2) (ψ := (539598077/5000000000 : ℝ)) half_20_09_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_09_bounds1 l).1) (fun l => (half_20_09_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_09_total1, half_20_09_total2, half_20_09_total3, half_20_09_total4, half_20_09_total5, half_20_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_09) (half_20_08)
    (by simpa only [half_20_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_20_09_hx2)
  exact h.weaken (by norm_num [half_20_09_total1, half_20_09_total2, half_20_09_total3, half_20_09_total4, half_20_09_total5, half_20_09_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_20_09 : AdmissibleExponent 9 40 (311610864603/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 18) (ψ := (1087187623/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_19_09)
    (by simpa only [half_20_09_φ1] using half_20_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_20_09_total1, half_20_09_total2, half_20_09_total3, half_20_09_total4, half_20_09_total5, half_20_09_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_21_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (273362583/2500000000 : ℝ)

private theorem half_21_09_total1 : total half_21_09_φ1=(273362583/2500000000 : ℝ) := by
  norm_num [half_21_09_φ1,total,emptyPhi,Fin.snoc]

private theorem half_21_09_bounds1 : ∀ l,0≤half_21_09_φ1 l ∧ half_21_09_φ1 l≤1 ∧
    0≤shiftExponents 9 half_21_09_φ1 l :=
  alternate_bounds_snoc emptyPhi (273362583/2500000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_21_09_φ2 : Fin 2 → ℝ := Fin.snoc half_21_09_φ1 (1087803463/10000000000 : ℝ)

private theorem half_21_09_total2 : total half_21_09_φ2=(436250759/2000000000 : ℝ) := by
  change total (Fin.snoc half_21_09_φ1 (1087803463/10000000000 : ℝ))=(436250759/2000000000 : ℝ)
  rw [alternate_total_snoc,half_21_09_total1]
  norm_num

private theorem half_21_09_bounds2 : ∀ l,0≤half_21_09_φ2 l ∧ half_21_09_φ2 l≤1 ∧
    0≤shiftExponents 9 half_21_09_φ2 l :=
  alternate_bounds_snoc half_21_09_φ1 (1087803463/10000000000 : ℝ) half_21_09_bounds1 (by norm_num)

private def half_21_09_φ3 : Fin 3 → ℝ := Fin.snoc half_21_09_φ2 (39093731/400000000 : ℝ)

private theorem half_21_09_total3 : total half_21_09_φ3=(315859707/1000000000 : ℝ) := by
  change total (Fin.snoc half_21_09_φ2 (39093731/400000000 : ℝ))=(315859707/1000000000 : ℝ)
  rw [alternate_total_snoc,half_21_09_total2]
  norm_num

private theorem half_21_09_bounds3 : ∀ l,0≤half_21_09_φ3 l ∧ half_21_09_φ3 l≤1 ∧
    0≤shiftExponents 9 half_21_09_φ3 l :=
  alternate_bounds_snoc half_21_09_φ2 (39093731/400000000 : ℝ) half_21_09_bounds2 (by norm_num)

private def half_21_09_φ4 : Fin 4 → ℝ := Fin.snoc half_21_09_φ3 (427587683/5000000000 : ℝ)

private theorem half_21_09_total4 : total half_21_09_φ4=(1003443109/2500000000 : ℝ) := by
  change total (Fin.snoc half_21_09_φ3 (427587683/5000000000 : ℝ))=(1003443109/2500000000 : ℝ)
  rw [alternate_total_snoc,half_21_09_total3]
  norm_num

private theorem half_21_09_bounds4 : ∀ l,0≤half_21_09_φ4 l ∧ half_21_09_φ4 l≤1 ∧
    0≤shiftExponents 9 half_21_09_φ4 l :=
  alternate_bounds_snoc half_21_09_φ3 (427587683/5000000000 : ℝ) half_21_09_bounds3 (by norm_num)

private def half_21_09_φ5 : Fin 5 → ℝ := Fin.snoc half_21_09_φ4 (149655689/2000000000 : ℝ)

private theorem half_21_09_total5 : total half_21_09_φ5=(4762050881/10000000000 : ℝ) := by
  change total (Fin.snoc half_21_09_φ4 (149655689/2000000000 : ℝ))=(4762050881/10000000000 : ℝ)
  rw [alternate_total_snoc,half_21_09_total4]
  norm_num

private theorem half_21_09_bounds5 : ∀ l,0≤half_21_09_φ5 l ∧ half_21_09_φ5 l≤1 ∧
    0≤shiftExponents 9 half_21_09_φ5 l :=
  alternate_bounds_snoc half_21_09_φ4 (149655689/2000000000 : ℝ) half_21_09_bounds4 (by norm_num)

private def half_21_09_φ6 : Fin 6 → ℝ := Fin.snoc half_21_09_φ5 (654743639/10000000000 : ℝ)

private theorem half_21_09_total6 : total half_21_09_φ6=(135419863/250000000 : ℝ) := by
  change total (Fin.snoc half_21_09_φ5 (654743639/10000000000 : ℝ))=(135419863/250000000 : ℝ)
  rw [alternate_total_snoc,half_21_09_total5]
  norm_num

private theorem half_21_09_bounds6 : ∀ l,0≤half_21_09_φ6 l ∧ half_21_09_φ6 l≤1 ∧
    0≤shiftExponents 9 half_21_09_φ6 l :=
  alternate_bounds_snoc half_21_09_φ5 (654743639/10000000000 : ℝ) half_21_09_bounds5 (by norm_num)

private theorem half_21_09_prefix : PrefixCondition 9 half_21_09_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_21_09_φ1, half_21_09_φ2, half_21_09_φ3, half_21_09_φ4, half_21_09_φ5, half_21_09_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_21_09_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_21_09_φ6) (218740411/31250000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_21_09_φ6
    (fun i => (half_21_09_bounds6 i).1) (fun i => (half_21_09_bounds6 i).2.1)
    (fun i => (half_21_09_bounds6 i).2.2) half_21_09_prefix
  convert h using 1 <;> norm_num [half_21_09_total1, half_21_09_total2, half_21_09_total3, half_21_09_total4, half_21_09_total5, half_21_09_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_21_09_hx6 : SourcePowerBound
    (powerBoxCross 9 15 64 half_21_09_φ6) (124612479551/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 15) (r := 2) (v := 0) (w := 20) (D := 64)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_21_09_φ6 (by norm_num [half_21_09_total1, half_21_09_total2, half_21_09_total3, half_21_09_total4, half_21_09_total5, half_21_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_21_09_total1, half_21_09_total2, half_21_09_total3, half_21_09_total4, half_21_09_total5, half_21_09_total6, parameterExponent, curveLoss, dyadicExponent]) half_21_09_hF2
    (admissibleExponent_zero 9) (half_20_09)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_21_09_total1, half_21_09_total2, half_21_09_total3, half_21_09_total4, half_21_09_total5, half_21_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_09_hx5 : SourcePowerBound
    (powerBoxCross 9 16 32 half_21_09_φ5) (18013160303/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 16) (u := 14) (t := 17)
    (D := 32) (ψ := (654743639/10000000000 : ℝ)) half_21_09_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_09_bounds5 l).1) (fun l => (half_21_09_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_09_total1, half_21_09_total2, half_21_09_total3, half_21_09_total4, half_21_09_total5, half_21_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_09) (half_17_09)
    (by simpa only [half_21_09_φ6, show (2:ℝ)*32=64 by norm_num] using half_21_09_hx6)
  exact h.weaken (by norm_num [half_21_09_total1, half_21_09_total2, half_21_09_total3, half_21_09_total4, half_21_09_total5, half_21_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_09_hx4 : SourcePowerBound
    (powerBoxCross 9 17 16 half_21_09_φ4) (169193724451/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 17) (u := 15) (t := 18)
    (D := 16) (ψ := (149655689/2000000000 : ℝ)) half_21_09_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_09_bounds4 l).1) (fun l => (half_21_09_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_09_total1, half_21_09_total2, half_21_09_total3, half_21_09_total4, half_21_09_total5, half_21_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_09) (half_18_09)
    (by simpa only [half_21_09_φ5, show (2:ℝ)*16=32 by norm_num] using half_21_09_hx5)
  exact h.weaken (by norm_num [half_21_09_total1, half_21_09_total2, half_21_09_total3, half_21_09_total4, half_21_09_total5, half_21_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_09_hx3 : SourcePowerBound
    (powerBoxCross 9 18 8 half_21_09_φ3) (50243522239/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 18) (u := 16) (t := 19)
    (D := 8) (ψ := (427587683/5000000000 : ℝ)) half_21_09_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_09_bounds3 l).1) (fun l => (half_21_09_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_09_total1, half_21_09_total2, half_21_09_total3, half_21_09_total4, half_21_09_total5, half_21_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_09) (half_19_09)
    (by simpa only [half_21_09_φ4, show (2:ℝ)*8=16 by norm_num] using half_21_09_hx4)
  exact h.weaken (by norm_num [half_21_09_total1, half_21_09_total2, half_21_09_total3, half_21_09_total4, half_21_09_total5, half_21_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_09_hx2 : SourcePowerBound
    (powerBoxCross 9 19 4 half_21_09_φ2) (30085731233/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 19) (u := 17) (t := 20)
    (D := 4) (ψ := (39093731/400000000 : ℝ)) half_21_09_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_09_bounds2 l).1) (fun l => (half_21_09_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_09_total1, half_21_09_total2, half_21_09_total3, half_21_09_total4, half_21_09_total5, half_21_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_09) (half_20_09)
    (by simpa only [half_21_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_21_09_hx3)
  exact h.weaken (by norm_num [half_21_09_total1, half_21_09_total2, half_21_09_total3, half_21_09_total4, half_21_09_total5, half_21_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_09_hx1 : SourcePowerBound
    (powerBoxCross 9 20 2 half_21_09_φ1) (288631214607/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 20) (u := 18) (t := 21)
    (D := 2) (ψ := (1087803463/10000000000 : ℝ)) half_21_09_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_09_bounds1 l).1) (fun l => (half_21_09_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_09_total1, half_21_09_total2, half_21_09_total3, half_21_09_total4, half_21_09_total5, half_21_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_19_09) (half_21_08)
    (by simpa only [half_21_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_21_09_hx2)
  exact h.weaken (by norm_num [half_21_09_total1, half_21_09_total2, half_21_09_total3, half_21_09_total4, half_21_09_total5, half_21_09_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_21_09 : AdmissibleExponent 9 42 (66255155511/2000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 19) (ψ := (273362583/2500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_20_09)
    (by simpa only [half_21_09_φ1] using half_21_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_21_09_total1, half_21_09_total2, half_21_09_total3, half_21_09_total4, half_21_09_total5, half_21_09_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_22_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (549252973/5000000000 : ℝ)

private theorem half_22_09_total1 : total half_22_09_φ1=(549252973/5000000000 : ℝ) := by
  norm_num [half_22_09_φ1,total,emptyPhi,Fin.snoc]

private theorem half_22_09_bounds1 : ∀ l,0≤half_22_09_φ1 l ∧ half_22_09_φ1 l≤1 ∧
    0≤shiftExponents 9 half_22_09_φ1 l :=
  alternate_bounds_snoc emptyPhi (549252973/5000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_22_09_φ2 : Fin 2 → ℝ := Fin.snoc half_22_09_φ1 (8756843/80000000 : ℝ)

private theorem half_22_09_total2 : total half_22_09_φ2=(2193111321/10000000000 : ℝ) := by
  change total (Fin.snoc half_22_09_φ1 (8756843/80000000 : ℝ))=(2193111321/10000000000 : ℝ)
  rw [alternate_total_snoc,half_22_09_total1]
  norm_num

private theorem half_22_09_bounds2 : ∀ l,0≤half_22_09_φ2 l ∧ half_22_09_φ2 l≤1 ∧
    0≤shiftExponents 9 half_22_09_φ2 l :=
  alternate_bounds_snoc half_22_09_φ1 (8756843/80000000 : ℝ) half_22_09_bounds1 (by norm_num)

private def half_22_09_φ3 : Fin 3 → ℝ := Fin.snoc half_22_09_φ2 (243965271/2500000000 : ℝ)

private theorem half_22_09_total3 : total half_22_09_φ3=(633794481/2000000000 : ℝ) := by
  change total (Fin.snoc half_22_09_φ2 (243965271/2500000000 : ℝ))=(633794481/2000000000 : ℝ)
  rw [alternate_total_snoc,half_22_09_total2]
  norm_num

private theorem half_22_09_bounds3 : ∀ l,0≤half_22_09_φ3 l ∧ half_22_09_φ3 l≤1 ∧
    0≤shiftExponents 9 half_22_09_φ3 l :=
  alternate_bounds_snoc half_22_09_φ2 (243965271/2500000000 : ℝ) half_22_09_bounds2 (by norm_num)

private def half_22_09_φ4 : Fin 4 → ℝ := Fin.snoc half_22_09_φ3 (853878449/10000000000 : ℝ)

private theorem half_22_09_total4 : total half_22_09_φ4=(2011425427/5000000000 : ℝ) := by
  change total (Fin.snoc half_22_09_φ3 (853878449/10000000000 : ℝ))=(2011425427/5000000000 : ℝ)
  rw [alternate_total_snoc,half_22_09_total3]
  norm_num

private theorem half_22_09_bounds4 : ∀ l,0≤half_22_09_φ4 l ∧ half_22_09_φ4 l≤1 ∧
    0≤shiftExponents 9 half_22_09_φ4 l :=
  alternate_bounds_snoc half_22_09_φ3 (853878449/10000000000 : ℝ) half_22_09_bounds3 (by norm_num)

private def half_22_09_φ5 : Fin 5 → ℝ := Fin.snoc half_22_09_φ4 (747143643/10000000000 : ℝ)

private theorem half_22_09_total5 : total half_22_09_φ5=(4769994497/10000000000 : ℝ) := by
  change total (Fin.snoc half_22_09_φ4 (747143643/10000000000 : ℝ))=(4769994497/10000000000 : ℝ)
  rw [alternate_total_snoc,half_22_09_total4]
  norm_num

private theorem half_22_09_bounds5 : ∀ l,0≤half_22_09_φ5 l ∧ half_22_09_φ5 l≤1 ∧
    0≤shiftExponents 9 half_22_09_φ5 l :=
  alternate_bounds_snoc half_22_09_φ4 (747143643/10000000000 : ℝ) half_22_09_bounds4 (by norm_num)

private def half_22_09_φ6 : Fin 6 → ℝ := Fin.snoc half_22_09_φ5 (653750687/10000000000 : ℝ)

private theorem half_22_09_total6 : total half_22_09_φ6=(169492037/312500000 : ℝ) := by
  change total (Fin.snoc half_22_09_φ5 (653750687/10000000000 : ℝ))=(169492037/312500000 : ℝ)
  rw [alternate_total_snoc,half_22_09_total5]
  norm_num

private theorem half_22_09_bounds6 : ∀ l,0≤half_22_09_φ6 l ∧ half_22_09_φ6 l≤1 ∧
    0≤shiftExponents 9 half_22_09_φ6 l :=
  alternate_bounds_snoc half_22_09_φ5 (653750687/10000000000 : ℝ) half_22_09_bounds5 (by norm_num)

private theorem half_22_09_prefix : PrefixCondition 9 half_22_09_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_22_09_φ1, half_22_09_φ2, half_22_09_φ3, half_22_09_φ4, half_22_09_φ5, half_22_09_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_22_09_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_22_09_φ6) (272773889/39062500 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_22_09_φ6
    (fun i => (half_22_09_bounds6 i).1) (fun i => (half_22_09_bounds6 i).2.1)
    (fun i => (half_22_09_bounds6 i).2.2) half_22_09_prefix
  convert h using 1 <;> norm_num [half_22_09_total1, half_22_09_total2, half_22_09_total3, half_22_09_total4, half_22_09_total5, half_22_09_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_22_09_hx6 : SourcePowerBound
    (powerBoxCross 9 16 64 half_22_09_φ6) (13342009163/1000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 16) (r := 2) (v := 21) (w := 22) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_22_09_φ6 (by norm_num [half_22_09_total1, half_22_09_total2, half_22_09_total3, half_22_09_total4, half_22_09_total5, half_22_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_22_09_total1, half_22_09_total2, half_22_09_total3, half_22_09_total4, half_22_09_total5, half_22_09_total6, parameterExponent, curveLoss, dyadicExponent]) half_22_09_hF2
    (half_21_09) (half_22_08)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_22_09_total1, half_22_09_total2, half_22_09_total3, half_22_09_total4, half_22_09_total5, half_22_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_09_hx5 : SourcePowerBound
    (powerBoxCross 9 17 32 half_22_09_φ5) (38513262387/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 17) (u := 15) (t := 18)
    (D := 32) (ψ := (653750687/10000000000 : ℝ)) half_22_09_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_09_bounds5 l).1) (fun l => (half_22_09_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_09_total1, half_22_09_total2, half_22_09_total3, half_22_09_total4, half_22_09_total5, half_22_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_09) (half_18_09)
    (by simpa only [half_22_09_φ6, show (2:ℝ)*32=64 by norm_num] using half_22_09_hx6)
  exact h.weaken (by norm_num [half_22_09_total1, half_22_09_total2, half_22_09_total3, half_22_09_total4, half_22_09_total5, half_22_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_09_hx4 : SourcePowerBound
    (powerBoxCross 9 18 16 half_22_09_φ4) (22567999143/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 18) (u := 16) (t := 19)
    (D := 16) (ψ := (747143643/10000000000 : ℝ)) half_22_09_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_09_bounds4 l).1) (fun l => (half_22_09_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_09_total1, half_22_09_total2, half_22_09_total3, half_22_09_total4, half_22_09_total5, half_22_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_09) (half_19_09)
    (by simpa only [half_22_09_φ5, show (2:ℝ)*16=32 by norm_num] using half_22_09_hx5)
  exact h.weaken (by norm_num [half_22_09_total1, half_22_09_total2, half_22_09_total3, half_22_09_total4, half_22_09_total5, half_22_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_09_hx3 : SourcePowerBound
    (powerBoxCross 9 19 8 half_22_09_φ3) (2674626257/125000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 19) (u := 17) (t := 20)
    (D := 8) (ψ := (853878449/10000000000 : ℝ)) half_22_09_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_09_bounds3 l).1) (fun l => (half_22_09_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_09_total1, half_22_09_total2, half_22_09_total3, half_22_09_total4, half_22_09_total5, half_22_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_09) (half_20_09)
    (by simpa only [half_22_09_φ4, show (2:ℝ)*8=16 by norm_num] using half_22_09_hx4)
  exact h.weaken (by norm_num [half_22_09_total1, half_22_09_total2, half_22_09_total3, half_22_09_total4, half_22_09_total5, half_22_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_09_hx2 : SourcePowerBound
    (powerBoxCross 9 20 4 half_22_09_φ2) (127788845461/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 20) (u := 18) (t := 21)
    (D := 4) (ψ := (243965271/2500000000 : ℝ)) half_22_09_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_09_bounds2 l).1) (fun l => (half_22_09_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_09_total1, half_22_09_total2, half_22_09_total3, half_22_09_total4, half_22_09_total5, half_22_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_19_09) (half_21_09)
    (by simpa only [half_22_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_22_09_hx3)
  exact h.weaken (by norm_num [half_22_09_total1, half_22_09_total2, half_22_09_total3, half_22_09_total4, half_22_09_total5, half_22_09_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_09_hx1 : SourcePowerBound
    (powerBoxCross 9 21 2 half_22_09_φ1) (4780991287/156250000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 21) (u := 19) (t := 22)
    (D := 2) (ψ := (8756843/80000000 : ℝ)) half_22_09_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_09_bounds1 l).1) (fun l => (half_22_09_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_09_total1, half_22_09_total2, half_22_09_total3, half_22_09_total4, half_22_09_total5, half_22_09_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_20_09) (half_22_08)
    (by simpa only [half_22_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_22_09_hx2)
  exact h.weaken (by norm_num [half_22_09_total1, half_22_09_total2, half_22_09_total3, half_22_09_total4, half_22_09_total5, half_22_09_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_22_09 : AdmissibleExponent 9 44 (175511093077/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 20) (ψ := (549252973/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_21_09)
    (by simpa only [half_22_09_φ1] using half_22_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_22_09_total1, half_22_09_total2, half_22_09_total3, half_22_09_total4, half_22_09_total5, half_22_09_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_10_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (220140247/2500000000 : ℝ)

private theorem half_10_10_total1 : total half_10_10_φ1=(220140247/2500000000 : ℝ) := by
  norm_num [half_10_10_φ1,total,emptyPhi,Fin.snoc]

private theorem half_10_10_bounds1 : ∀ l,0≤half_10_10_φ1 l ∧ half_10_10_φ1 l≤1 ∧
    0≤shiftExponents 9 half_10_10_φ1 l :=
  alternate_bounds_snoc emptyPhi (220140247/2500000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_10_10_φ2 : Fin 2 → ℝ := Fin.snoc half_10_10_φ1 (821568559/10000000000 : ℝ)

private theorem half_10_10_total2 : total half_10_10_φ2=(1702129547/10000000000 : ℝ) := by
  change total (Fin.snoc half_10_10_φ1 (821568559/10000000000 : ℝ))=(1702129547/10000000000 : ℝ)
  rw [alternate_total_snoc,half_10_10_total1]
  norm_num

private theorem half_10_10_bounds2 : ∀ l,0≤half_10_10_φ2 l ∧ half_10_10_φ2 l≤1 ∧
    0≤shiftExponents 9 half_10_10_φ2 l :=
  alternate_bounds_snoc half_10_10_φ1 (821568559/10000000000 : ℝ) half_10_10_bounds1 (by norm_num)

private def half_10_10_φ3 : Fin 3 → ℝ := Fin.snoc half_10_10_φ2 (717048371/10000000000 : ℝ)

private theorem half_10_10_total3 : total half_10_10_φ3=(1209588959/5000000000 : ℝ) := by
  change total (Fin.snoc half_10_10_φ2 (717048371/10000000000 : ℝ))=(1209588959/5000000000 : ℝ)
  rw [alternate_total_snoc,half_10_10_total2]
  norm_num

private theorem half_10_10_bounds3 : ∀ l,0≤half_10_10_φ3 l ∧ half_10_10_φ3 l≤1 ∧
    0≤shiftExponents 9 half_10_10_φ3 l :=
  alternate_bounds_snoc half_10_10_φ2 (717048371/10000000000 : ℝ) half_10_10_bounds2 (by norm_num)

private def half_10_10_φ4 : Fin 4 → ℝ := Fin.snoc half_10_10_φ3 (450214159/10000000000 : ℝ)

private theorem half_10_10_total4 : total half_10_10_φ4=(2869392077/10000000000 : ℝ) := by
  change total (Fin.snoc half_10_10_φ3 (450214159/10000000000 : ℝ))=(2869392077/10000000000 : ℝ)
  rw [alternate_total_snoc,half_10_10_total3]
  norm_num

private theorem half_10_10_bounds4 : ∀ l,0≤half_10_10_φ4 l ∧ half_10_10_φ4 l≤1 ∧
    0≤shiftExponents 9 half_10_10_φ4 l :=
  alternate_bounds_snoc half_10_10_φ3 (450214159/10000000000 : ℝ) half_10_10_bounds3 (by norm_num)

private theorem half_10_10_prefix : PrefixCondition 9 half_10_10_φ4 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_10_10_φ1, half_10_10_φ2, half_10_10_φ3, half_10_10_φ4, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_10_10_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 16 half_10_10_φ4) (8891823769/1250000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 9) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_10_φ4
    (fun i => (half_10_10_bounds4 i).1) (fun i => (half_10_10_bounds4 i).2.1)
    (fun i => (half_10_10_bounds4 i).2.2) half_10_10_prefix
  convert h using 1 <;> norm_num [half_10_10_total1, half_10_10_total2, half_10_10_total3, half_10_10_total4, parameterExponent, curveLoss, dyadicExponent]

private theorem half_10_10_hx4 : SourcePowerBound
    (powerBoxCross 9 6 16 half_10_10_φ4) (6914502601/1000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 6) (r := 2) (v := 0) (w := 8) (D := 16)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_10_10_φ4 (by norm_num [half_10_10_total1, half_10_10_total2, half_10_10_total3, half_10_10_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_10_10_total1, half_10_10_total2, half_10_10_total3, half_10_10_total4, parameterExponent, curveLoss, dyadicExponent]) half_10_10_hF2
    (admissibleExponent_zero 9) (SeedCompletionHigher9SimpleSeeds.degree9_half_8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_10_total1, half_10_10_total2, half_10_10_total3, half_10_10_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_10_10_hx3 : SourcePowerBound
    (powerBoxCross 9 7 8 half_10_10_φ3) (78774810149/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 7) (u := 5) (t := 8)
    (D := 8) (ψ := (450214159/10000000000 : ℝ)) half_10_10_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_10_10_bounds3 l).1) (fun l => (half_10_10_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_10_10_total1, half_10_10_total2, half_10_10_total3, half_10_10_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_6) (SeedCompletionHigher9SimpleSeeds.degree9_half_8)
    (by simpa only [half_10_10_φ4, show (2:ℝ)*8=16 by norm_num] using half_10_10_hx4)
  exact h.weaken (by norm_num [half_10_10_total1, half_10_10_total2, half_10_10_total3, half_10_10_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_10_10_hx2 : SourcePowerBound
    (powerBoxCross 9 8 4 half_10_10_φ2) (46734611377/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (717048371/10000000000 : ℝ)) half_10_10_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_10_10_bounds2 l).1) (fun l => (half_10_10_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_10_10_total1, half_10_10_total2, half_10_10_total3, half_10_10_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_7) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_10_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_10_hx3)
  exact h.weaken (by norm_num [half_10_10_total1, half_10_10_total2, half_10_10_total3, half_10_10_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_10_10_hx1 : SourcePowerBound
    (powerBoxCross 9 9 2 half_10_10_φ1) (878858857/78125000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (821568559/10000000000 : ℝ)) half_10_10_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_10_10_bounds1 l).1) (fun l => (half_10_10_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_10_10_total1, half_10_10_total2, half_10_10_total3, half_10_10_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_09)
    (by simpa only [half_10_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_10_hx2)
  exact h.weaken (by norm_num [half_10_10_total1, half_10_10_total2, half_10_10_total3, half_10_10_total4, parameterExponent, curveLoss, dyadicExponent])

theorem half_10_10 : AdmissibleExponent 9 20 (31865867623/2500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 8) (ψ := (220140247/2500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_10_10_φ1] using half_10_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_10_total1, half_10_10_total2, half_10_10_total3, half_10_10_total4, parameterExponent, curveLoss, dyadicExponent])

private def half_11_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (915763457/10000000000 : ℝ)

private theorem half_11_10_total1 : total half_11_10_φ1=(915763457/10000000000 : ℝ) := by
  norm_num [half_11_10_φ1,total,emptyPhi,Fin.snoc]

private theorem half_11_10_bounds1 : ∀ l,0≤half_11_10_φ1 l ∧ half_11_10_φ1 l≤1 ∧
    0≤shiftExponents 9 half_11_10_φ1 l :=
  alternate_bounds_snoc emptyPhi (915763457/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_11_10_φ2 : Fin 2 → ℝ := Fin.snoc half_11_10_φ1 (27043851/312500000 : ℝ)

private theorem half_11_10_total2 : total half_11_10_φ2=(1781166689/10000000000 : ℝ) := by
  change total (Fin.snoc half_11_10_φ1 (27043851/312500000 : ℝ))=(1781166689/10000000000 : ℝ)
  rw [alternate_total_snoc,half_11_10_total1]
  norm_num

private theorem half_11_10_bounds2 : ∀ l,0≤half_11_10_φ2 l ∧ half_11_10_φ2 l≤1 ∧
    0≤shiftExponents 9 half_11_10_φ2 l :=
  alternate_bounds_snoc half_11_10_φ1 (27043851/312500000 : ℝ) half_11_10_bounds1 (by norm_num)

private def half_11_10_φ3 : Fin 3 → ℝ := Fin.snoc half_11_10_φ2 (157622467/2000000000 : ℝ)

private theorem half_11_10_total3 : total half_11_10_φ3=(160579939/625000000 : ℝ) := by
  change total (Fin.snoc half_11_10_φ2 (157622467/2000000000 : ℝ))=(160579939/625000000 : ℝ)
  rw [alternate_total_snoc,half_11_10_total2]
  norm_num

private theorem half_11_10_bounds3 : ∀ l,0≤half_11_10_φ3 l ∧ half_11_10_φ3 l≤1 ∧
    0≤shiftExponents 9 half_11_10_φ3 l :=
  alternate_bounds_snoc half_11_10_φ2 (157622467/2000000000 : ℝ) half_11_10_bounds2 (by norm_num)

private def half_11_10_φ4 : Fin 4 → ℝ := Fin.snoc half_11_10_φ3 (624750909/10000000000 : ℝ)

private theorem half_11_10_total4 : total half_11_10_φ4=(3194029933/10000000000 : ℝ) := by
  change total (Fin.snoc half_11_10_φ3 (624750909/10000000000 : ℝ))=(3194029933/10000000000 : ℝ)
  rw [alternate_total_snoc,half_11_10_total3]
  norm_num

private theorem half_11_10_bounds4 : ∀ l,0≤half_11_10_φ4 l ∧ half_11_10_φ4 l≤1 ∧
    0≤shiftExponents 9 half_11_10_φ4 l :=
  alternate_bounds_snoc half_11_10_φ3 (624750909/10000000000 : ℝ) half_11_10_bounds3 (by norm_num)

private theorem half_11_10_prefix : PrefixCondition 9 half_11_10_φ4 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_11_10_φ1, half_11_10_φ2, half_11_10_φ3, half_11_10_φ4, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_11_10_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 16 half_11_10_φ4) (7917910201/1250000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 9) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_10_φ4
    (fun i => (half_11_10_bounds4 i).1) (fun i => (half_11_10_bounds4 i).2.1)
    (fun i => (half_11_10_bounds4 i).2.2) half_11_10_prefix
  convert h using 1 <;> norm_num [half_11_10_total1, half_11_10_total2, half_11_10_total3, half_11_10_total4, parameterExponent, curveLoss, dyadicExponent]

private theorem half_11_10_hx4 : SourcePowerBound
    (powerBoxCross 9 7 16 half_11_10_φ4) (7544140403/1000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 7) (r := 2) (v := 9) (w := 10) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_11_10_φ4 (by norm_num [half_11_10_total1, half_11_10_total2, half_11_10_total3, half_11_10_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_11_10_total1, half_11_10_total2, half_11_10_total3, half_11_10_total4, parameterExponent, curveLoss, dyadicExponent]) half_11_10_hF2
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_10_10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_10_total1, half_11_10_total2, half_11_10_total3, half_11_10_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_11_10_hx3 : SourcePowerBound
    (powerBoxCross 9 8 8 half_11_10_φ3) (43951440321/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (624750909/10000000000 : ℝ)) half_11_10_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_11_10_bounds3 l).1) (fun l => (half_11_10_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_11_10_total1, half_11_10_total2, half_11_10_total3, half_11_10_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_7) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_11_10_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_10_hx4)
  exact h.weaken (by norm_num [half_11_10_total1, half_11_10_total2, half_11_10_total3, half_11_10_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_11_10_hx2 : SourcePowerBound
    (powerBoxCross 9 9 4 half_11_10_φ2) (105117666939/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (157622467/2000000000 : ℝ)) half_11_10_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_11_10_bounds2 l).1) (fun l => (half_11_10_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_11_10_total1, half_11_10_total2, half_11_10_total3, half_11_10_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_10)
    (by simpa only [half_11_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_10_hx3)
  exact h.weaken (by norm_num [half_11_10_total1, half_11_10_total2, half_11_10_total3, half_11_10_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_11_10_hx1 : SourcePowerBound
    (powerBoxCross 9 10 2 half_11_10_φ1) (31676648779/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (27043851/312500000 : ℝ)) half_11_10_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_11_10_bounds1 l).1) (fun l => (half_11_10_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_11_10_total1, half_11_10_total2, half_11_10_total3, half_11_10_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_09)
    (by simpa only [half_11_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_10_hx2)
  exact h.weaken (by norm_num [half_11_10_total1, half_11_10_total2, half_11_10_total3, half_11_10_total4, parameterExponent, curveLoss, dyadicExponent])

theorem half_11_10 : AdmissibleExponent 9 22 (144106100799/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 9) (ψ := (915763457/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_10_10)
    (by simpa only [half_11_10_φ1] using half_11_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_10_total1, half_11_10_total2, half_11_10_total3, half_11_10_total4, parameterExponent, curveLoss, dyadicExponent])

private def half_12_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (94696533/1000000000 : ℝ)

private theorem half_12_10_total1 : total half_12_10_φ1=(94696533/1000000000 : ℝ) := by
  norm_num [half_12_10_φ1,total,emptyPhi,Fin.snoc]

private theorem half_12_10_bounds1 : ∀ l,0≤half_12_10_φ1 l ∧ half_12_10_φ1 l≤1 ∧
    0≤shiftExponents 9 half_12_10_φ1 l :=
  alternate_bounds_snoc emptyPhi (94696533/1000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_12_10_φ2 : Fin 2 → ℝ := Fin.snoc half_12_10_φ1 (903207329/10000000000 : ℝ)

private theorem half_12_10_total2 : total half_12_10_φ2=(1850172659/10000000000 : ℝ) := by
  change total (Fin.snoc half_12_10_φ1 (903207329/10000000000 : ℝ))=(1850172659/10000000000 : ℝ)
  rw [alternate_total_snoc,half_12_10_total1]
  norm_num

private theorem half_12_10_bounds2 : ∀ l,0≤half_12_10_φ2 l ∧ half_12_10_φ2 l≤1 ∧
    0≤shiftExponents 9 half_12_10_φ2 l :=
  alternate_bounds_snoc half_12_10_φ1 (903207329/10000000000 : ℝ) half_12_10_bounds1 (by norm_num)

private def half_12_10_φ3 : Fin 3 → ℝ := Fin.snoc half_12_10_φ2 (840733979/10000000000 : ℝ)

private theorem half_12_10_total3 : total half_12_10_φ3=(1345453319/5000000000 : ℝ) := by
  change total (Fin.snoc half_12_10_φ2 (840733979/10000000000 : ℝ))=(1345453319/5000000000 : ℝ)
  rw [alternate_total_snoc,half_12_10_total2]
  norm_num

private theorem half_12_10_bounds3 : ∀ l,0≤half_12_10_φ3 l ∧ half_12_10_φ3 l≤1 ∧
    0≤shiftExponents 9 half_12_10_φ3 l :=
  alternate_bounds_snoc half_12_10_φ2 (840733979/10000000000 : ℝ) half_12_10_bounds2 (by norm_num)

private def half_12_10_φ4 : Fin 4 → ℝ := Fin.snoc half_12_10_φ3 (727970927/10000000000 : ℝ)

private theorem half_12_10_total4 : total half_12_10_φ4=(683775513/2000000000 : ℝ) := by
  change total (Fin.snoc half_12_10_φ3 (727970927/10000000000 : ℝ))=(683775513/2000000000 : ℝ)
  rw [alternate_total_snoc,half_12_10_total3]
  norm_num

private theorem half_12_10_bounds4 : ∀ l,0≤half_12_10_φ4 l ∧ half_12_10_φ4 l≤1 ∧
    0≤shiftExponents 9 half_12_10_φ4 l :=
  alternate_bounds_snoc half_12_10_φ3 (727970927/10000000000 : ℝ) half_12_10_bounds3 (by norm_num)

private def half_12_10_φ5 : Fin 5 → ℝ := Fin.snoc half_12_10_φ4 (225167989/5000000000 : ℝ)

private theorem half_12_10_total5 : total half_12_10_φ5=(3869213543/10000000000 : ℝ) := by
  change total (Fin.snoc half_12_10_φ4 (225167989/5000000000 : ℝ))=(3869213543/10000000000 : ℝ)
  rw [alternate_total_snoc,half_12_10_total4]
  norm_num

private theorem half_12_10_bounds5 : ∀ l,0≤half_12_10_φ5 l ∧ half_12_10_φ5 l≤1 ∧
    0≤shiftExponents 9 half_12_10_φ5 l :=
  alternate_bounds_snoc half_12_10_φ4 (225167989/5000000000 : ℝ) half_12_10_bounds4 (by norm_num)

private theorem half_12_10_prefix : PrefixCondition 9 half_12_10_φ5 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_12_10_φ1, half_12_10_φ2, half_12_10_φ3, half_12_10_φ4, half_12_10_φ5, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_12_10_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 32 half_12_10_φ5) (9642359371/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_12_10_φ5
    (fun i => (half_12_10_bounds5 i).1) (fun i => (half_12_10_bounds5 i).2.1)
    (fun i => (half_12_10_bounds5 i).2.2) half_12_10_prefix
  convert h using 1 <;> norm_num [half_12_10_total1, half_12_10_total2, half_12_10_total3, half_12_10_total4, half_12_10_total5, parameterExponent, curveLoss, dyadicExponent]

private theorem half_12_10_hx5 : SourcePowerBound
    (powerBoxCross 9 7 32 half_12_10_φ5) (72977153659/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 7) (r := 2) (v := 9) (w := 10) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_12_10_φ5 (by norm_num [half_12_10_total1, half_12_10_total2, half_12_10_total3, half_12_10_total4, half_12_10_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_12_10_total1, half_12_10_total2, half_12_10_total3, half_12_10_total4, half_12_10_total5, parameterExponent, curveLoss, dyadicExponent]) half_12_10_hF2
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_10_10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_10_total1, half_12_10_total2, half_12_10_total3, half_12_10_total4, half_12_10_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_10_hx4 : SourcePowerBound
    (powerBoxCross 9 8 16 half_12_10_φ4) (3296213491/400000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 8) (u := 6) (t := 9)
    (D := 16) (ψ := (225167989/5000000000 : ℝ)) half_12_10_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_10_bounds4 l).1) (fun l => (half_12_10_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_10_total1, half_12_10_total2, half_12_10_total3, half_12_10_total4, half_12_10_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_7) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_12_10_φ5, show (2:ℝ)*16=32 by norm_num] using half_12_10_hx5)
  exact h.weaken (by norm_num [half_12_10_total1, half_12_10_total2, half_12_10_total3, half_12_10_total4, half_12_10_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_10_hx3 : SourcePowerBound
    (powerBoxCross 9 9 8 half_12_10_φ3) (48740472171/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (727970927/10000000000 : ℝ)) half_12_10_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_10_bounds3 l).1) (fun l => (half_12_10_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_10_total1, half_12_10_total2, half_12_10_total3, half_12_10_total4, half_12_10_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_10)
    (by simpa only [half_12_10_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_10_hx4)
  exact h.weaken (by norm_num [half_12_10_total1, half_12_10_total2, half_12_10_total3, half_12_10_total4, half_12_10_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_10_hx2 : SourcePowerBound
    (powerBoxCross 9 10 4 half_12_10_φ2) (29302003093/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (840733979/10000000000 : ℝ)) half_12_10_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_10_bounds2 l).1) (fun l => (half_12_10_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_10_total1, half_12_10_total2, half_12_10_total3, half_12_10_total4, half_12_10_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_10)
    (by simpa only [half_12_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_10_hx3)
  exact h.weaken (by norm_num [half_12_10_total1, half_12_10_total2, half_12_10_total3, half_12_10_total4, half_12_10_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_10_hx1 : SourcePowerBound
    (powerBoxCross 9 11 2 half_12_10_φ1) (141406718007/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (903207329/10000000000 : ℝ)) half_12_10_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_10_bounds1 l).1) (fun l => (half_12_10_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_10_total1, half_12_10_total2, half_12_10_total3, half_12_10_total4, half_12_10_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_10) (half_12_09)
    (by simpa only [half_12_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_10_hx2)
  exact h.weaken (by norm_num [half_12_10_total1, half_12_10_total2, half_12_10_total3, half_12_10_total4, half_12_10_total5, parameterExponent, curveLoss, dyadicExponent])

theorem half_12_10 : AdmissibleExponent 9 24 (161292989937/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 10) (ψ := (94696533/1000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_11_10)
    (by simpa only [half_12_10_φ1] using half_12_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_10_total1, half_12_10_total2, half_12_10_total3, half_12_10_total4, half_12_10_total5, parameterExponent, curveLoss, dyadicExponent])

end Waring.SeedCompletionAlternate9Seeds
