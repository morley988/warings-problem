import Waring.SeedCompletionAlternate9Steps12

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionAlternate9Seeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges SeedCompletionDivisorPowerScales
open PolicyCompletionSharpResidualSource

private def half_11_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (915736629/10000000000 : ℝ)

private theorem half_11_12_total1 : total half_11_12_φ1=(915736629/10000000000 : ℝ) := by
  norm_num [half_11_12_φ1,total,emptyPhi,Fin.snoc]

private theorem half_11_12_bounds1 : ∀ l,0≤half_11_12_φ1 l ∧ half_11_12_φ1 l≤1 ∧
    0≤shiftExponents 9 half_11_12_φ1 l :=
  alternate_bounds_snoc emptyPhi (915736629/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_11_12_φ2 : Fin 2 → ℝ := Fin.snoc half_11_12_φ1 (865401003/10000000000 : ℝ)

private theorem half_11_12_total2 : total half_11_12_φ2=(55660551/312500000 : ℝ) := by
  change total (Fin.snoc half_11_12_φ1 (865401003/10000000000 : ℝ))=(55660551/312500000 : ℝ)
  rw [alternate_total_snoc,half_11_12_total1]
  norm_num

private theorem half_11_12_bounds2 : ∀ l,0≤half_11_12_φ2 l ∧ half_11_12_φ2 l≤1 ∧
    0≤shiftExponents 9 half_11_12_φ2 l :=
  alternate_bounds_snoc half_11_12_φ1 (865401003/10000000000 : ℝ) half_11_12_bounds1 (by norm_num)

private def half_11_12_φ3 : Fin 3 → ℝ := Fin.snoc half_11_12_φ2 (788110369/10000000000 : ℝ)

private theorem half_11_12_total3 : total half_11_12_φ3=(2569248001/10000000000 : ℝ) := by
  change total (Fin.snoc half_11_12_φ2 (788110369/10000000000 : ℝ))=(2569248001/10000000000 : ℝ)
  rw [alternate_total_snoc,half_11_12_total2]
  norm_num

private theorem half_11_12_bounds3 : ∀ l,0≤half_11_12_φ3 l ∧ half_11_12_φ3 l≤1 ∧
    0≤shiftExponents 9 half_11_12_φ3 l :=
  alternate_bounds_snoc half_11_12_φ2 (788110369/10000000000 : ℝ) half_11_12_bounds2 (by norm_num)

private def half_11_12_φ4 : Fin 4 → ℝ := Fin.snoc half_11_12_φ3 (624744501/10000000000 : ℝ)

private theorem half_11_12_total4 : total half_11_12_φ4=(1596996251/5000000000 : ℝ) := by
  change total (Fin.snoc half_11_12_φ3 (624744501/10000000000 : ℝ))=(1596996251/5000000000 : ℝ)
  rw [alternate_total_snoc,half_11_12_total3]
  norm_num

private theorem half_11_12_bounds4 : ∀ l,0≤half_11_12_φ4 l ∧ half_11_12_φ4 l≤1 ∧
    0≤shiftExponents 9 half_11_12_φ4 l :=
  alternate_bounds_snoc half_11_12_φ3 (624744501/10000000000 : ℝ) half_11_12_bounds3 (by norm_num)

private theorem half_11_12_prefix : PrefixCondition 9 half_11_12_φ4 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, half_11_12_φ4, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_11_12_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 16 half_11_12_φ4) (3959011247/625000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 9) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_12_φ4
    (fun i => (half_11_12_bounds4 i).1) (fun i => (half_11_12_bounds4 i).2.1)
    (fun i => (half_11_12_bounds4 i).2.2) half_11_12_prefix
  convert h using 1 <;> norm_num [half_11_12_total1, half_11_12_total2, half_11_12_total3, half_11_12_total4, parameterExponent, curveLoss, dyadicExponent]

private theorem half_11_12_hx4 : SourcePowerBound
    (powerBoxCross 9 7 16 half_11_12_φ4) (15088390067/2000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 7) (r := 2) (v := 9) (w := 10) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_11_12_φ4 (by norm_num [half_11_12_total1, half_11_12_total2, half_11_12_total3, half_11_12_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_11_12_total1, half_11_12_total2, half_11_12_total3, half_11_12_total4, parameterExponent, curveLoss, dyadicExponent]) half_11_12_hF2
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_10_12)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_12_total1, half_11_12_total2, half_11_12_total3, half_11_12_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_11_12_hx3 : SourcePowerBound
    (powerBoxCross 9 8 8 half_11_12_φ3) (5493963067/625000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (624744501/10000000000 : ℝ)) half_11_12_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_11_12_bounds3 l).1) (fun l => (half_11_12_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_11_12_total1, half_11_12_total2, half_11_12_total3, half_11_12_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_7) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_11_12_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_12_hx4)
  exact h.weaken (by norm_num [half_11_12_total1, half_11_12_total2, half_11_12_total3, half_11_12_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_11_12_hx2 : SourcePowerBound
    (powerBoxCross 9 9 4 half_11_12_φ2) (1051182031/100000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (788110369/10000000000 : ℝ)) half_11_12_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_11_12_bounds2 l).1) (fun l => (half_11_12_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_11_12_total1, half_11_12_total2, half_11_12_total3, half_11_12_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_12)
    (by simpa only [half_11_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_12_hx3)
  exact h.weaken (by norm_num [half_11_12_total1, half_11_12_total2, half_11_12_total3, half_11_12_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_11_12_hx1 : SourcePowerBound
    (powerBoxCross 9 10 2 half_11_12_φ1) (31676719427/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (865401003/10000000000 : ℝ)) half_11_12_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_11_12_bounds1 l).1) (fun l => (half_11_12_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_11_12_total1, half_11_12_total2, half_11_12_total3, half_11_12_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_11)
    (by simpa only [half_11_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_12_hx2)
  exact h.weaken (by norm_num [half_11_12_total1, half_11_12_total2, half_11_12_total3, half_11_12_total4, parameterExponent, curveLoss, dyadicExponent])

theorem half_11_12 : AdmissibleExponent 9 22 (144105873659/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 9) (ψ := (915736629/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_10_12)
    (by simpa only [half_11_12_φ1] using half_11_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_12_total1, half_11_12_total2, half_11_12_total3, half_11_12_total4, parameterExponent, curveLoss, dyadicExponent])

private def half_12_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (946896397/10000000000 : ℝ)

private theorem half_12_12_total1 : total half_12_12_φ1=(946896397/10000000000 : ℝ) := by
  norm_num [half_12_12_φ1,total,emptyPhi,Fin.snoc]

private theorem half_12_12_bounds1 : ∀ l,0≤half_12_12_φ1 l ∧ half_12_12_φ1 l≤1 ∧
    0≤shiftExponents 9 half_12_12_φ1 l :=
  alternate_bounds_snoc emptyPhi (946896397/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_12_12_φ2 : Fin 2 → ℝ := Fin.snoc half_12_12_φ1 (903199441/10000000000 : ℝ)

private theorem half_12_12_total2 : total half_12_12_φ2=(925047919/5000000000 : ℝ) := by
  change total (Fin.snoc half_12_12_φ1 (903199441/10000000000 : ℝ))=(925047919/5000000000 : ℝ)
  rw [alternate_total_snoc,half_12_12_total1]
  norm_num

private theorem half_12_12_bounds2 : ∀ l,0≤half_12_12_φ2 l ∧ half_12_12_φ2 l≤1 ∧
    0≤shiftExponents 9 half_12_12_φ2 l :=
  alternate_bounds_snoc half_12_12_φ1 (903199441/10000000000 : ℝ) half_12_12_bounds1 (by norm_num)

private def half_12_12_φ3 : Fin 3 → ℝ := Fin.snoc half_12_12_φ2 (840731077/10000000000 : ℝ)

private theorem half_12_12_total3 : total half_12_12_φ3=(538165383/2000000000 : ℝ) := by
  change total (Fin.snoc half_12_12_φ2 (840731077/10000000000 : ℝ))=(538165383/2000000000 : ℝ)
  rw [alternate_total_snoc,half_12_12_total2]
  norm_num

private theorem half_12_12_bounds3 : ∀ l,0≤half_12_12_φ3 l ∧ half_12_12_φ3 l≤1 ∧
    0≤shiftExponents 9 half_12_12_φ3 l :=
  alternate_bounds_snoc half_12_12_φ2 (840731077/10000000000 : ℝ) half_12_12_bounds2 (by norm_num)

private def half_12_12_φ4 : Fin 4 → ℝ := Fin.snoc half_12_12_φ3 (18199151/250000000 : ℝ)

private theorem half_12_12_total4 : total half_12_12_φ4=(683758591/2000000000 : ℝ) := by
  change total (Fin.snoc half_12_12_φ3 (18199151/250000000 : ℝ))=(683758591/2000000000 : ℝ)
  rw [alternate_total_snoc,half_12_12_total3]
  norm_num

private theorem half_12_12_bounds4 : ∀ l,0≤half_12_12_φ4 l ∧ half_12_12_φ4 l≤1 ∧
    0≤shiftExponents 9 half_12_12_φ4 l :=
  alternate_bounds_snoc half_12_12_φ3 (18199151/250000000 : ℝ) half_12_12_bounds3 (by norm_num)

private def half_12_12_φ5 : Fin 5 → ℝ := Fin.snoc half_12_12_φ4 (450319963/10000000000 : ℝ)

private theorem half_12_12_total5 : total half_12_12_φ5=(1934556459/5000000000 : ℝ) := by
  change total (Fin.snoc half_12_12_φ4 (450319963/10000000000 : ℝ))=(1934556459/5000000000 : ℝ)
  rw [alternate_total_snoc,half_12_12_total4]
  norm_num

private theorem half_12_12_bounds5 : ∀ l,0≤half_12_12_φ5 l ∧ half_12_12_φ5 l≤1 ∧
    0≤shiftExponents 9 half_12_12_φ5 l :=
  alternate_bounds_snoc half_12_12_φ4 (450319963/10000000000 : ℝ) half_12_12_bounds4 (by norm_num)

private theorem half_12_12_prefix : PrefixCondition 9 half_12_12_φ5 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, half_12_12_φ5, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_12_12_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 32 half_12_12_φ5) (4821330623/625000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_12_12_φ5
    (fun i => (half_12_12_bounds5 i).1) (fun i => (half_12_12_bounds5 i).2.1)
    (fun i => (half_12_12_bounds5 i).2.2) half_12_12_prefix
  convert h using 1 <;> norm_num [half_12_12_total1, half_12_12_total2, half_12_12_total3, half_12_12_total4, half_12_12_total5, parameterExponent, curveLoss, dyadicExponent]

private theorem half_12_12_hx5 : SourcePowerBound
    (powerBoxCross 9 7 32 half_12_12_φ5) (2919145327/400000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 7) (r := 2) (v := 9) (w := 10) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_12_12_φ5 (by norm_num [half_12_12_total1, half_12_12_total2, half_12_12_total3, half_12_12_total4, half_12_12_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_12_12_total1, half_12_12_total2, half_12_12_total3, half_12_12_total4, half_12_12_total5, parameterExponent, curveLoss, dyadicExponent]) half_12_12_hF2
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_10_12)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_12_total1, half_12_12_total2, half_12_12_total3, half_12_12_total4, half_12_12_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_12_hx4 : SourcePowerBound
    (powerBoxCross 9 8 16 half_12_12_φ4) (82406782759/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 8) (u := 6) (t := 9)
    (D := 16) (ψ := (450319963/10000000000 : ℝ)) half_12_12_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_12_bounds4 l).1) (fun l => (half_12_12_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_12_total1, half_12_12_total2, half_12_12_total3, half_12_12_total4, half_12_12_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_7) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_12_12_φ5, show (2:ℝ)*16=32 by norm_num] using half_12_12_hx5)
  exact h.weaken (by norm_num [half_12_12_total1, half_12_12_total2, half_12_12_total3, half_12_12_total4, half_12_12_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_12_hx3 : SourcePowerBound
    (powerBoxCross 9 9 8 half_12_12_φ3) (97482444319/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (18199151/250000000 : ℝ)) half_12_12_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_12_bounds3 l).1) (fun l => (half_12_12_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_12_total1, half_12_12_total2, half_12_12_total3, half_12_12_total4, half_12_12_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_12)
    (by simpa only [half_12_12_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_12_hx4)
  exact h.weaken (by norm_num [half_12_12_total1, half_12_12_total2, half_12_12_total3, half_12_12_total4, half_12_12_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_12_hx2 : SourcePowerBound
    (powerBoxCross 9 10 4 half_12_12_φ2) (58604752969/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (840731077/10000000000 : ℝ)) half_12_12_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_12_bounds2 l).1) (fun l => (half_12_12_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_12_total1, half_12_12_total2, half_12_12_total3, half_12_12_total4, half_12_12_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_12)
    (by simpa only [half_12_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_12_hx3)
  exact h.weaken (by norm_num [half_12_12_total1, half_12_12_total2, half_12_12_total3, half_12_12_total4, half_12_12_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_12_hx1 : SourcePowerBound
    (powerBoxCross 9 11 2 half_12_12_φ1) (141407436803/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (903199441/10000000000 : ℝ)) half_12_12_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_12_bounds1 l).1) (fun l => (half_12_12_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_12_total1, half_12_12_total2, half_12_12_total3, half_12_12_total4, half_12_12_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_12) (half_12_11)
    (by simpa only [half_12_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_12_hx2)
  exact h.weaken (by norm_num [half_12_12_total1, half_12_12_total2, half_12_12_total3, half_12_12_total4, half_12_12_total5, parameterExponent, curveLoss, dyadicExponent])

theorem half_12_12 : AdmissibleExponent 9 24 (8064613057/500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 10) (ψ := (946896397/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_11_12)
    (by simpa only [half_12_12_φ1] using half_12_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_12_total1, half_12_12_total2, half_12_12_total3, half_12_12_total4, half_12_12_total5, parameterExponent, curveLoss, dyadicExponent])

private def half_13_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (974197093/10000000000 : ℝ)

private theorem half_13_12_total1 : total half_13_12_φ1=(974197093/10000000000 : ℝ) := by
  norm_num [half_13_12_φ1,total,emptyPhi,Fin.snoc]

private theorem half_13_12_bounds1 : ∀ l,0≤half_13_12_φ1 l ∧ half_13_12_φ1 l≤1 ∧
    0≤shiftExponents 9 half_13_12_φ1 l :=
  alternate_bounds_snoc emptyPhi (974197093/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_13_12_φ2 : Fin 2 → ℝ := Fin.snoc half_13_12_φ1 (467800163/5000000000 : ℝ)

private theorem half_13_12_total2 : total half_13_12_φ2=(1909797419/10000000000 : ℝ) := by
  change total (Fin.snoc half_13_12_φ1 (467800163/5000000000 : ℝ))=(1909797419/10000000000 : ℝ)
  rw [alternate_total_snoc,half_13_12_total1]
  norm_num

private theorem half_13_12_bounds2 : ∀ l,0≤half_13_12_φ2 l ∧ half_13_12_φ2 l≤1 ∧
    0≤shiftExponents 9 half_13_12_φ2 l :=
  alternate_bounds_snoc half_13_12_φ1 (467800163/5000000000 : ℝ) half_13_12_bounds1 (by norm_num)

private def half_13_12_φ3 : Fin 3 → ℝ := Fin.snoc half_13_12_φ2 (220603929/2500000000 : ℝ)

private theorem half_13_12_total3 : total half_13_12_φ3=(558442627/2000000000 : ℝ) := by
  change total (Fin.snoc half_13_12_φ2 (220603929/2500000000 : ℝ))=(558442627/2000000000 : ℝ)
  rw [alternate_total_snoc,half_13_12_total2]
  norm_num

private theorem half_13_12_bounds3 : ∀ l,0≤half_13_12_φ3 l ∧ half_13_12_φ3 l≤1 ∧
    0≤shiftExponents 9 half_13_12_φ3 l :=
  alternate_bounds_snoc half_13_12_φ2 (220603929/2500000000 : ℝ) half_13_12_bounds2 (by norm_num)

private def half_13_12_φ4 : Fin 4 → ℝ := Fin.snoc half_13_12_φ3 (794475089/10000000000 : ℝ)

private theorem half_13_12_total4 : total half_13_12_φ4=(112084007/312500000 : ℝ) := by
  change total (Fin.snoc half_13_12_φ3 (794475089/10000000000 : ℝ))=(112084007/312500000 : ℝ)
  rw [alternate_total_snoc,half_13_12_total3]
  norm_num

private theorem half_13_12_bounds4 : ∀ l,0≤half_13_12_φ4 l ∧ half_13_12_φ4 l≤1 ∧
    0≤shiftExponents 9 half_13_12_φ4 l :=
  alternate_bounds_snoc half_13_12_φ3 (794475089/10000000000 : ℝ) half_13_12_bounds3 (by norm_num)

private def half_13_12_φ5 : Fin 5 → ℝ := Fin.snoc half_13_12_φ4 (303466269/5000000000 : ℝ)

private theorem half_13_12_total5 : total half_13_12_φ5=(2096810381/5000000000 : ℝ) := by
  change total (Fin.snoc half_13_12_φ4 (303466269/5000000000 : ℝ))=(2096810381/5000000000 : ℝ)
  rw [alternate_total_snoc,half_13_12_total4]
  norm_num

private theorem half_13_12_bounds5 : ∀ l,0≤half_13_12_φ5 l ∧ half_13_12_φ5 l≤1 ∧
    0≤shiftExponents 9 half_13_12_φ5 l :=
  alternate_bounds_snoc half_13_12_φ4 (303466269/5000000000 : ℝ) half_13_12_bounds4 (by norm_num)

private theorem half_13_12_prefix : PrefixCondition 9 half_13_12_φ5 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, half_13_12_φ5, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_13_12_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 32 half_13_12_φ5) (4334568857/625000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_13_12_φ5
    (fun i => (half_13_12_bounds5 i).1) (fun i => (half_13_12_bounds5 i).2.1)
    (fun i => (half_13_12_bounds5 i).2.2) half_13_12_prefix
  convert h using 1 <;> norm_num [half_13_12_total1, half_13_12_total2, half_13_12_total3, half_13_12_total4, half_13_12_total5, parameterExponent, curveLoss, dyadicExponent]

private theorem half_13_12_hx5 : SourcePowerBound
    (powerBoxCross 9 8 32 half_13_12_φ5) (77677469089/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 8) (r := 2) (v := 10) (w := 11) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_13_12_φ5 (by norm_num [half_13_12_total1, half_13_12_total2, half_13_12_total3, half_13_12_total4, half_13_12_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_13_12_total1, half_13_12_total2, half_13_12_total3, half_13_12_total4, half_13_12_total5, parameterExponent, curveLoss, dyadicExponent]) half_13_12_hF2
    (half_10_12) (half_11_12)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_12_total1, half_13_12_total2, half_13_12_total3, half_13_12_total4, half_13_12_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_12_hx4 : SourcePowerBound
    (powerBoxCross 9 9 16 half_13_12_φ4) (22479278253/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (303466269/5000000000 : ℝ)) half_13_12_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_12_bounds4 l).1) (fun l => (half_13_12_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_12_total1, half_13_12_total2, half_13_12_total3, half_13_12_total4, half_13_12_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_12)
    (by simpa only [half_13_12_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_12_hx5)
  exact h.weaken (by norm_num [half_13_12_total1, half_13_12_total2, half_13_12_total3, half_13_12_total4, half_13_12_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_12_hx3 : SourcePowerBound
    (powerBoxCross 9 10 8 half_13_12_φ3) (107476963389/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (794475089/10000000000 : ℝ)) half_13_12_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_12_bounds3 l).1) (fun l => (half_13_12_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_12_total1, half_13_12_total2, half_13_12_total3, half_13_12_total4, half_13_12_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_12)
    (by simpa only [half_13_12_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_12_hx4)
  exact h.weaken (by norm_num [half_13_12_total1, half_13_12_total2, half_13_12_total3, half_13_12_total4, half_13_12_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_12_hx2 : SourcePowerBound
    (powerBoxCross 9 11 4 half_13_12_φ2) (12972659469/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (220603929/2500000000 : ℝ)) half_13_12_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_12_bounds2 l).1) (fun l => (half_13_12_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_12_total1, half_13_12_total2, half_13_12_total3, half_13_12_total4, half_13_12_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_12) (half_12_12)
    (by simpa only [half_13_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_12_hx3)
  exact h.weaken (by norm_num [half_13_12_total1, half_13_12_total2, half_13_12_total3, half_13_12_total4, half_13_12_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_12_hx1 : SourcePowerBound
    (powerBoxCross 9 12 2 half_13_12_φ1) (39138353261/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (467800163/5000000000 : ℝ)) half_13_12_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_12_bounds1 l).1) (fun l => (half_13_12_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_12_total1, half_13_12_total2, half_13_12_total3, half_13_12_total4, half_13_12_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_12) (half_13_11)
    (by simpa only [half_13_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_12_hx2)
  exact h.weaken (by norm_num [half_13_12_total1, half_13_12_total2, half_13_12_total3, half_13_12_total4, half_13_12_total5, parameterExponent, curveLoss, dyadicExponent])

theorem half_13_12 : AdmissibleExponent 9 26 (178959946183/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 11) (ψ := (974197093/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_12_12)
    (by simpa only [half_13_12_φ1] using half_13_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_12_total1, half_13_12_total2, half_13_12_total3, half_13_12_total4, half_13_12_total5, parameterExponent, curveLoss, dyadicExponent])

private def half_14_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (999129487/10000000000 : ℝ)

private theorem half_14_12_total1 : total half_14_12_φ1=(999129487/10000000000 : ℝ) := by
  norm_num [half_14_12_φ1,total,emptyPhi,Fin.snoc]

private theorem half_14_12_bounds1 : ∀ l,0≤half_14_12_φ1 l ∧ half_14_12_φ1 l≤1 ∧
    0≤shiftExponents 9 half_14_12_φ1 l :=
  alternate_bounds_snoc emptyPhi (999129487/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_14_12_φ2 : Fin 2 → ℝ := Fin.snoc half_14_12_φ1 (193043757/2000000000 : ℝ)

private theorem half_14_12_total2 : total half_14_12_φ2=(122771767/625000000 : ℝ) := by
  change total (Fin.snoc half_14_12_φ1 (193043757/2000000000 : ℝ))=(122771767/625000000 : ℝ)
  rw [alternate_total_snoc,half_14_12_total1]
  norm_num

private theorem half_14_12_bounds2 : ∀ l,0≤half_14_12_φ2 l ∧ half_14_12_φ2 l≤1 ∧
    0≤shiftExponents 9 half_14_12_φ2 l :=
  alternate_bounds_snoc half_14_12_φ1 (193043757/2000000000 : ℝ) half_14_12_bounds1 (by norm_num)

private def half_14_12_φ3 : Fin 3 → ℝ := Fin.snoc half_14_12_φ2 (92064887/1000000000 : ℝ)

private theorem half_14_12_total3 : total half_14_12_φ3=(1442498571/5000000000 : ℝ) := by
  change total (Fin.snoc half_14_12_φ2 (92064887/1000000000 : ℝ))=(1442498571/5000000000 : ℝ)
  rw [alternate_total_snoc,half_14_12_total2]
  norm_num

private theorem half_14_12_bounds3 : ∀ l,0≤half_14_12_φ3 l ∧ half_14_12_φ3 l≤1 ∧
    0≤shiftExponents 9 half_14_12_φ3 l :=
  alternate_bounds_snoc half_14_12_φ2 (92064887/1000000000 : ℝ) half_14_12_bounds2 (by norm_num)

private def half_14_12_φ4 : Fin 4 → ℝ := Fin.snoc half_14_12_φ3 (852626553/10000000000 : ℝ)

private theorem half_14_12_total4 : total half_14_12_φ4=(747524739/2000000000 : ℝ) := by
  change total (Fin.snoc half_14_12_φ3 (852626553/10000000000 : ℝ))=(747524739/2000000000 : ℝ)
  rw [alternate_total_snoc,half_14_12_total3]
  norm_num

private theorem half_14_12_bounds4 : ∀ l,0≤half_14_12_φ4 l ∧ half_14_12_φ4 l≤1 ∧
    0≤shiftExponents 9 half_14_12_φ4 l :=
  alternate_bounds_snoc half_14_12_φ3 (852626553/10000000000 : ℝ) half_14_12_bounds3 (by norm_num)

private def half_14_12_φ5 : Fin 5 → ℝ := Fin.snoc half_14_12_φ4 (144922011/2000000000 : ℝ)

private theorem half_14_12_total5 : total half_14_12_φ5=(3569787/8000000 : ℝ) := by
  change total (Fin.snoc half_14_12_φ4 (144922011/2000000000 : ℝ))=(3569787/8000000 : ℝ)
  rw [alternate_total_snoc,half_14_12_total4]
  norm_num

private theorem half_14_12_bounds5 : ∀ l,0≤half_14_12_φ5 l ∧ half_14_12_φ5 l≤1 ∧
    0≤shiftExponents 9 half_14_12_φ5 l :=
  alternate_bounds_snoc half_14_12_φ4 (144922011/2000000000 : ℝ) half_14_12_bounds4 (by norm_num)

private def half_14_12_φ6 : Fin 6 → ℝ := Fin.snoc half_14_12_φ5 (419250523/10000000000 : ℝ)

private theorem half_14_12_total6 : total half_14_12_φ6=(4881484273/10000000000 : ℝ) := by
  change total (Fin.snoc half_14_12_φ5 (419250523/10000000000 : ℝ))=(4881484273/10000000000 : ℝ)
  rw [alternate_total_snoc,half_14_12_total5]
  norm_num

private theorem half_14_12_bounds6 : ∀ l,0≤half_14_12_φ6 l ∧ half_14_12_φ6 l≤1 ∧
    0≤shiftExponents 9 half_14_12_φ6 l :=
  alternate_bounds_snoc half_14_12_φ5 (419250523/10000000000 : ℝ) half_14_12_bounds5 (by norm_num)

private theorem half_14_12_prefix : PrefixCondition 9 half_14_12_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, half_14_12_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_14_12_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_14_12_φ6) (10355547181/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_14_12_φ6
    (fun i => (half_14_12_bounds6 i).1) (fun i => (half_14_12_bounds6 i).2.1)
    (fun i => (half_14_12_bounds6 i).2.2) half_14_12_prefix
  convert h using 1 <;> norm_num [half_14_12_total1, half_14_12_total2, half_14_12_total3, half_14_12_total4, half_14_12_total5, half_14_12_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_14_12_hF1 : SourcePowerBound
    (paddedMoment 9 0 1 64 half_14_12_φ6) (3868515727/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_14_12_φ6
    (fun i => (half_14_12_bounds6 i).1) (fun i => (half_14_12_bounds6 i).2.1)
    (fun i => (half_14_12_bounds6 i).2.2) half_14_12_prefix
  convert h using 1 <;> norm_num [half_14_12_total1, half_14_12_total2, half_14_12_total3, half_14_12_total4, half_14_12_total5, half_14_12_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_14_12_hx6 : SourcePowerBound
    (powerBoxCross 9 8 64 half_14_12_φ6) (18469807979/2500000000 : ℝ) := by
  have h := full_B_cross_power (k := 9) (s := 8) (r := 1) (v := 2) (t := 11) (D := 64)
    (a := (1/22 : ℝ)) (b := (5/22 : ℝ)) (c := (8/11 : ℝ))
    (by norm_num) half_14_12_φ6 (by norm_num [half_14_12_total1, half_14_12_total2, half_14_12_total3, half_14_12_total4, half_14_12_total5, half_14_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_14_12_total1, half_14_12_total2, half_14_12_total3, half_14_12_total4, half_14_12_total5, half_14_12_total6, parameterExponent, curveLoss, dyadicExponent]) half_14_12_hF1 half_14_12_hF2
    (half_11_12)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_12_total1, half_14_12_total2, half_14_12_total3, half_14_12_total4, half_14_12_total5, half_14_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_12_hx5 : SourcePowerBound
    (powerBoxCross 9 9 32 half_14_12_φ5) (20632048803/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 9) (u := 7) (t := 10)
    (D := 32) (ψ := (419250523/10000000000 : ℝ)) half_14_12_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_12_bounds5 l).1) (fun l => (half_14_12_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_12_total1, half_14_12_total2, half_14_12_total3, half_14_12_total4, half_14_12_total5, half_14_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_12)
    (by simpa only [half_14_12_φ6, show (2:ℝ)*32=64 by norm_num] using half_14_12_hx6)
  exact h.weaken (by norm_num [half_14_12_total1, half_14_12_total2, half_14_12_total3, half_14_12_total4, half_14_12_total5, half_14_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_12_hx4 : SourcePowerBound
    (powerBoxCross 9 10 16 half_14_12_φ4) (3903801949/400000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (144922011/2000000000 : ℝ)) half_14_12_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_12_bounds4 l).1) (fun l => (half_14_12_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_12_total1, half_14_12_total2, half_14_12_total3, half_14_12_total4, half_14_12_total5, half_14_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_12)
    (by simpa only [half_14_12_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_12_hx5)
  exact h.weaken (by norm_num [half_14_12_total1, half_14_12_total2, half_14_12_total3, half_14_12_total4, half_14_12_total5, half_14_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_12_hx3 : SourcePowerBound
    (powerBoxCross 9 11 8 half_14_12_φ3) (58868616499/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (852626553/10000000000 : ℝ)) half_14_12_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_12_bounds3 l).1) (fun l => (half_14_12_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_12_total1, half_14_12_total2, half_14_12_total3, half_14_12_total4, half_14_12_total5, half_14_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_12) (half_12_12)
    (by simpa only [half_14_12_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_12_hx4)
  exact h.weaken (by norm_num [half_14_12_total1, half_14_12_total2, half_14_12_total3, half_14_12_total4, half_14_12_total5, half_14_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_12_hx2 : SourcePowerBound
    (powerBoxCross 9 12 4 half_14_12_φ2) (71290513293/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (92064887/1000000000 : ℝ)) half_14_12_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_12_bounds2 l).1) (fun l => (half_14_12_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_12_total1, half_14_12_total2, half_14_12_total3, half_14_12_total4, half_14_12_total5, half_14_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_12) (half_13_12)
    (by simpa only [half_14_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_12_hx3)
  exact h.weaken (by norm_num [half_14_12_total1, half_14_12_total2, half_14_12_total3, half_14_12_total4, half_14_12_total5, half_14_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_12_hx1 : SourcePowerBound
    (powerBoxCross 9 13 2 half_14_12_φ1) (43019664939/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (193043757/2000000000 : ℝ)) half_14_12_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_12_bounds1 l).1) (fun l => (half_14_12_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_12_total1, half_14_12_total2, half_14_12_total3, half_14_12_total4, half_14_12_total5, half_14_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_12) (half_14_11)
    (by simpa only [half_14_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_12_hx2)
  exact h.weaken (by norm_num [half_14_12_total1, half_14_12_total2, half_14_12_total3, half_14_12_total4, half_14_12_total5, half_14_12_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_14_12 : AdmissibleExponent 9 28 (197056896931/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 12) (ψ := (999129487/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_13_12)
    (by simpa only [half_14_12_φ1] using half_14_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_12_total1, half_14_12_total2, half_14_12_total3, half_14_12_total4, half_14_12_total5, half_14_12_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_15_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1019412283/10000000000 : ℝ)

private theorem half_15_12_total1 : total half_15_12_φ1=(1019412283/10000000000 : ℝ) := by
  norm_num [half_15_12_φ1,total,emptyPhi,Fin.snoc]

private theorem half_15_12_bounds1 : ∀ l,0≤half_15_12_φ1 l ∧ half_15_12_φ1 l≤1 ∧
    0≤shiftExponents 9 half_15_12_φ1 l :=
  alternate_bounds_snoc emptyPhi (1019412283/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_15_12_φ2 : Fin 2 → ℝ := Fin.snoc half_15_12_φ1 (990375653/10000000000 : ℝ)

private theorem half_15_12_total2 : total half_15_12_φ2=(62805873/312500000 : ℝ) := by
  change total (Fin.snoc half_15_12_φ1 (990375653/10000000000 : ℝ))=(62805873/312500000 : ℝ)
  rw [alternate_total_snoc,half_15_12_total1]
  norm_num

private theorem half_15_12_bounds2 : ∀ l,0≤half_15_12_φ2 l ∧ half_15_12_φ2 l≤1 ∧
    0≤shiftExponents 9 half_15_12_φ2 l :=
  alternate_bounds_snoc half_15_12_φ1 (990375653/10000000000 : ℝ) half_15_12_bounds1 (by norm_num)

private def half_15_12_φ3 : Fin 3 → ℝ := Fin.snoc half_15_12_φ2 (475415091/5000000000 : ℝ)

private theorem half_15_12_total3 : total half_15_12_φ3=(1480309059/5000000000 : ℝ) := by
  change total (Fin.snoc half_15_12_φ2 (475415091/5000000000 : ℝ))=(1480309059/5000000000 : ℝ)
  rw [alternate_total_snoc,half_15_12_total2]
  norm_num

private theorem half_15_12_bounds3 : ∀ l,0≤half_15_12_φ3 l ∧ half_15_12_φ3 l≤1 ∧
    0≤shiftExponents 9 half_15_12_φ3 l :=
  alternate_bounds_snoc half_15_12_φ2 (475415091/5000000000 : ℝ) half_15_12_bounds2 (by norm_num)

private def half_15_12_φ4 : Fin 4 → ℝ := Fin.snoc half_15_12_φ3 (175984547/2000000000 : ℝ)

private theorem half_15_12_total4 : total half_15_12_φ4=(3840540853/10000000000 : ℝ) := by
  change total (Fin.snoc half_15_12_φ3 (175984547/2000000000 : ℝ))=(3840540853/10000000000 : ℝ)
  rw [alternate_total_snoc,half_15_12_total3]
  norm_num

private theorem half_15_12_bounds4 : ∀ l,0≤half_15_12_φ4 l ∧ half_15_12_φ4 l≤1 ∧
    0≤shiftExponents 9 half_15_12_φ4 l :=
  alternate_bounds_snoc half_15_12_φ3 (175984547/2000000000 : ℝ) half_15_12_bounds3 (by norm_num)

private def half_15_12_φ5 : Fin 5 → ℝ := Fin.snoc half_15_12_φ4 (769932393/10000000000 : ℝ)

private theorem half_15_12_total5 : total half_15_12_φ5=(2305236623/5000000000 : ℝ) := by
  change total (Fin.snoc half_15_12_φ4 (769932393/10000000000 : ℝ))=(2305236623/5000000000 : ℝ)
  rw [alternate_total_snoc,half_15_12_total4]
  norm_num

private theorem half_15_12_bounds5 : ∀ l,0≤half_15_12_φ5 l ∧ half_15_12_φ5 l≤1 ∧
    0≤shiftExponents 9 half_15_12_φ5 l :=
  alternate_bounds_snoc half_15_12_φ4 (769932393/10000000000 : ℝ) half_15_12_bounds4 (by norm_num)

private def half_15_12_φ6 : Fin 6 → ℝ := Fin.snoc half_15_12_φ5 (68590861/1250000000 : ℝ)

private theorem half_15_12_total6 : total half_15_12_φ6=(2579600067/5000000000 : ℝ) := by
  change total (Fin.snoc half_15_12_φ5 (68590861/1250000000 : ℝ))=(2579600067/5000000000 : ℝ)
  rw [alternate_total_snoc,half_15_12_total5]
  norm_num

private theorem half_15_12_bounds6 : ∀ l,0≤half_15_12_φ6 l ∧ half_15_12_φ6 l≤1 ∧
    0≤shiftExponents 9 half_15_12_φ6 l :=
  alternate_bounds_snoc half_15_12_φ5 (68590861/1250000000 : ℝ) half_15_12_bounds5 (by norm_num)

private theorem half_15_12_prefix : PrefixCondition 9 half_15_12_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, half_15_12_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_15_12_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_15_12_φ6) (4761199799/625000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_15_12_φ6
    (fun i => (half_15_12_bounds6 i).1) (fun i => (half_15_12_bounds6 i).2.1)
    (fun i => (half_15_12_bounds6 i).2.2) half_15_12_prefix
  convert h using 1 <;> norm_num [half_15_12_total1, half_15_12_total2, half_15_12_total3, half_15_12_total4, half_15_12_total5, half_15_12_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_15_12_hx6 : SourcePowerBound
    (powerBoxCross 9 9 64 half_15_12_φ6) (15520713181/2000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 9) (r := 2) (v := 0) (w := 12) (D := 64)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_15_12_φ6 (by norm_num [half_15_12_total1, half_15_12_total2, half_15_12_total3, half_15_12_total4, half_15_12_total5, half_15_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_15_12_total1, half_15_12_total2, half_15_12_total3, half_15_12_total4, half_15_12_total5, half_15_12_total6, parameterExponent, curveLoss, dyadicExponent]) half_15_12_hF2
    (admissibleExponent_zero 9) (half_12_12)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_12_total1, half_15_12_total2, half_15_12_total3, half_15_12_total4, half_15_12_total5, half_15_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_12_hx5 : SourcePowerBound
    (powerBoxCross 9 10 32 half_15_12_φ5) (11107148949/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 10) (u := 8) (t := 11)
    (D := 32) (ψ := (68590861/1250000000 : ℝ)) half_15_12_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_12_bounds5 l).1) (fun l => (half_15_12_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_12_total1, half_15_12_total2, half_15_12_total3, half_15_12_total4, half_15_12_total5, half_15_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_12)
    (by simpa only [half_15_12_φ6, show (2:ℝ)*32=64 by norm_num] using half_15_12_hx6)
  exact h.weaken (by norm_num [half_15_12_total1, half_15_12_total2, half_15_12_total3, half_15_12_total4, half_15_12_total5, half_15_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_12_hx4 : SourcePowerBound
    (powerBoxCross 9 11 16 half_15_12_φ4) (106054444779/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (769932393/10000000000 : ℝ)) half_15_12_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_12_bounds4 l).1) (fun l => (half_15_12_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_12_total1, half_15_12_total2, half_15_12_total3, half_15_12_total4, half_15_12_total5, half_15_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_12) (half_12_12)
    (by simpa only [half_15_12_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_12_hx5)
  exact h.weaken (by norm_num [half_15_12_total1, half_15_12_total2, half_15_12_total3, half_15_12_total4, half_15_12_total5, half_15_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_12_hx3 : SourcePowerBound
    (powerBoxCross 9 12 8 half_15_12_φ3) (64206154387/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (175984547/2000000000 : ℝ)) half_15_12_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_12_bounds3 l).1) (fun l => (half_15_12_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_12_total1, half_15_12_total2, half_15_12_total3, half_15_12_total4, half_15_12_total5, half_15_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_12) (half_13_12)
    (by simpa only [half_15_12_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_12_hx4)
  exact h.weaken (by norm_num [half_15_12_total1, half_15_12_total2, half_15_12_total3, half_15_12_total4, half_15_12_total5, half_15_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_12_hx2 : SourcePowerBound
    (powerBoxCross 9 13 4 half_15_12_φ2) (77913934747/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (475415091/5000000000 : ℝ)) half_15_12_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_12_bounds2 l).1) (fun l => (half_15_12_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_12_total1, half_15_12_total2, half_15_12_total3, half_15_12_total4, half_15_12_total5, half_15_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_12) (half_14_12)
    (by simpa only [half_15_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_12_hx3)
  exact h.weaken (by norm_num [half_15_12_total1, half_15_12_total2, half_15_12_total3, half_15_12_total4, half_15_12_total5, half_15_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_12_hx1 : SourcePowerBound
    (powerBoxCross 9 14 2 half_15_12_φ1) (2937313861/156250000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (990375653/10000000000 : ℝ)) half_15_12_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_12_bounds1 l).1) (fun l => (half_15_12_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_12_total1, half_15_12_total2, half_15_12_total3, half_15_12_total4, half_15_12_total5, half_15_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_12) (half_15_11)
    (by simpa only [half_15_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_12_hx2)
  exact h.weaken (by norm_num [half_15_12_total1, half_15_12_total2, half_15_12_total3, half_15_12_total4, half_15_12_total5, half_15_12_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_15_12 : AdmissibleExponent 9 30 (43102443749/2000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 13) (ψ := (1019412283/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_14_12)
    (by simpa only [half_15_12_φ1] using half_15_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_12_total1, half_15_12_total2, half_15_12_total3, half_15_12_total4, half_15_12_total5, half_15_12_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_16_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1038926839/10000000000 : ℝ)

private theorem half_16_12_total1 : total half_16_12_φ1=(1038926839/10000000000 : ℝ) := by
  norm_num [half_16_12_φ1,total,emptyPhi,Fin.snoc]

private theorem half_16_12_bounds1 : ∀ l,0≤half_16_12_φ1 l ∧ half_16_12_φ1 l≤1 ∧
    0≤shiftExponents 9 half_16_12_φ1 l :=
  alternate_bounds_snoc emptyPhi (1038926839/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_16_12_φ2 : Fin 2 → ℝ := Fin.snoc half_16_12_φ1 (506943829/5000000000 : ℝ)

private theorem half_16_12_total2 : total half_16_12_φ2=(2052814497/10000000000 : ℝ) := by
  change total (Fin.snoc half_16_12_φ1 (506943829/5000000000 : ℝ))=(2052814497/10000000000 : ℝ)
  rw [alternate_total_snoc,half_16_12_total1]
  norm_num

private theorem half_16_12_bounds2 : ∀ l,0≤half_16_12_φ2 l ∧ half_16_12_φ2 l≤1 ∧
    0≤shiftExponents 9 half_16_12_φ2 l :=
  alternate_bounds_snoc half_16_12_φ1 (506943829/5000000000 : ℝ) half_16_12_bounds1 (by norm_num)

private def half_16_12_φ3 : Fin 3 → ℝ := Fin.snoc half_16_12_φ2 (24571719/250000000 : ℝ)

private theorem half_16_12_total3 : total half_16_12_φ3=(3035683257/10000000000 : ℝ) := by
  change total (Fin.snoc half_16_12_φ2 (24571719/250000000 : ℝ))=(3035683257/10000000000 : ℝ)
  rw [alternate_total_snoc,half_16_12_total2]
  norm_num

private theorem half_16_12_bounds3 : ∀ l,0≤half_16_12_φ3 l ∧ half_16_12_φ3 l≤1 ∧
    0≤shiftExponents 9 half_16_12_φ3 l :=
  alternate_bounds_snoc half_16_12_φ2 (24571719/250000000 : ℝ) half_16_12_bounds2 (by norm_num)

private def half_16_12_φ4 : Fin 4 → ℝ := Fin.snoc half_16_12_φ3 (108817449/1250000000 : ℝ)

private theorem half_16_12_total4 : total half_16_12_φ4=(3906222849/10000000000 : ℝ) := by
  change total (Fin.snoc half_16_12_φ3 (108817449/1250000000 : ℝ))=(3906222849/10000000000 : ℝ)
  rw [alternate_total_snoc,half_16_12_total3]
  norm_num

private theorem half_16_12_bounds4 : ∀ l,0≤half_16_12_φ4 l ∧ half_16_12_φ4 l≤1 ∧
    0≤shiftExponents 9 half_16_12_φ4 l :=
  alternate_bounds_snoc half_16_12_φ3 (108817449/1250000000 : ℝ) half_16_12_bounds3 (by norm_num)

private def half_16_12_φ5 : Fin 5 → ℝ := Fin.snoc half_16_12_φ4 (761722143/10000000000 : ℝ)

private theorem half_16_12_total5 : total half_16_12_φ5=(145873281/312500000 : ℝ) := by
  change total (Fin.snoc half_16_12_φ4 (761722143/10000000000 : ℝ))=(145873281/312500000 : ℝ)
  rw [alternate_total_snoc,half_16_12_total4]
  norm_num

private theorem half_16_12_bounds5 : ∀ l,0≤half_16_12_φ5 l ∧ half_16_12_φ5 l≤1 ∧
    0≤shiftExponents 9 half_16_12_φ5 l :=
  alternate_bounds_snoc half_16_12_φ4 (761722143/10000000000 : ℝ) half_16_12_bounds4 (by norm_num)

private def half_16_12_φ6 : Fin 6 → ℝ := Fin.snoc half_16_12_φ5 (16457937/250000000 : ℝ)

private theorem half_16_12_total6 : total half_16_12_φ6=(665782809/1250000000 : ℝ) := by
  change total (Fin.snoc half_16_12_φ5 (16457937/250000000 : ℝ))=(665782809/1250000000 : ℝ)
  rw [alternate_total_snoc,half_16_12_total5]
  norm_num

private theorem half_16_12_bounds6 : ∀ l,0≤half_16_12_φ6 l ∧ half_16_12_φ6 l≤1 ∧
    0≤shiftExponents 9 half_16_12_φ6 l :=
  alternate_bounds_snoc half_16_12_φ5 (16457937/250000000 : ℝ) half_16_12_bounds5 (by norm_num)

private theorem half_16_12_prefix : PrefixCondition 9 half_16_12_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, half_16_12_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_16_12_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_16_12_φ6) (1127651573/156250000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_16_12_φ6
    (fun i => (half_16_12_bounds6 i).1) (fun i => (half_16_12_bounds6 i).2.1)
    (fun i => (half_16_12_bounds6 i).2.2) half_16_12_prefix
  convert h using 1 <;> norm_num [half_16_12_total1, half_16_12_total2, half_16_12_total3, half_16_12_total4, half_16_12_total5, half_16_12_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_16_12_hx6 : SourcePowerBound
    (powerBoxCross 9 10 64 half_16_12_φ6) (82887821351/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 10) (r := 2) (v := 13) (w := 14) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_16_12_φ6 (by norm_num [half_16_12_total1, half_16_12_total2, half_16_12_total3, half_16_12_total4, half_16_12_total5, half_16_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_16_12_total1, half_16_12_total2, half_16_12_total3, half_16_12_total4, half_16_12_total5, half_16_12_total6, parameterExponent, curveLoss, dyadicExponent]) half_16_12_hF2
    (half_13_12) (half_14_12)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_12_total1, half_16_12_total2, half_16_12_total3, half_16_12_total4, half_16_12_total5, half_16_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_12_hx5 : SourcePowerBound
    (powerBoxCross 9 11 32 half_16_12_φ5) (48513553603/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 11) (u := 9) (t := 12)
    (D := 32) (ψ := (16457937/250000000 : ℝ)) half_16_12_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_12_bounds5 l).1) (fun l => (half_16_12_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_12_total1, half_16_12_total2, half_16_12_total3, half_16_12_total4, half_16_12_total5, half_16_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_12) (half_12_12)
    (by simpa only [half_16_12_φ6, show (2:ℝ)*32=64 by norm_num] using half_16_12_hx6)
  exact h.weaken (by norm_num [half_16_12_total1, half_16_12_total2, half_16_12_total3, half_16_12_total4, half_16_12_total5, half_16_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_12_hx4 : SourcePowerBound
    (powerBoxCross 9 12 16 half_16_12_φ4) (115413846259/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (761722143/10000000000 : ℝ)) half_16_12_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_12_bounds4 l).1) (fun l => (half_16_12_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_12_total1, half_16_12_total2, half_16_12_total3, half_16_12_total4, half_16_12_total5, half_16_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_12) (half_13_12)
    (by simpa only [half_16_12_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_12_hx5)
  exact h.weaken (by norm_num [half_16_12_total1, half_16_12_total2, half_16_12_total3, half_16_12_total4, half_16_12_total5, half_16_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_12_hx3 : SourcePowerBound
    (powerBoxCross 9 13 8 half_16_12_φ3) (139193727741/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (108817449/1250000000 : ℝ)) half_16_12_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_12_bounds3 l).1) (fun l => (half_16_12_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_12_total1, half_16_12_total2, half_16_12_total3, half_16_12_total4, half_16_12_total5, half_16_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_12) (half_14_12)
    (by simpa only [half_16_12_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_12_hx4)
  exact h.weaken (by norm_num [half_16_12_total1, half_16_12_total2, half_16_12_total3, half_16_12_total4, half_16_12_total5, half_16_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_12_hx2 : SourcePowerBound
    (powerBoxCross 9 14 4 half_16_12_φ2) (169307244409/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (24571719/250000000 : ℝ)) half_16_12_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_12_bounds2 l).1) (fun l => (half_16_12_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_12_total1, half_16_12_total2, half_16_12_total3, half_16_12_total4, half_16_12_total5, half_16_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_12) (half_15_12)
    (by simpa only [half_16_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_12_hx3)
  exact h.weaken (by norm_num [half_16_12_total1, half_16_12_total2, half_16_12_total3, half_16_12_total4, half_16_12_total5, half_16_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_12_hx1 : SourcePowerBound
    (powerBoxCross 9 15 2 half_16_12_φ1) (204161002769/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (506943829/5000000000 : ℝ)) half_16_12_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_12_bounds1 l).1) (fun l => (half_16_12_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_12_total1, half_16_12_total2, half_16_12_total3, half_16_12_total4, half_16_12_total5, half_16_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_12) (half_16_11)
    (by simpa only [half_16_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_12_hx2)
  exact h.weaken (by norm_num [half_16_12_total1, half_16_12_total2, half_16_12_total3, half_16_12_total4, half_16_12_total5, half_16_12_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_16_12 : AdmissibleExponent 9 32 (2342898811/100000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 14) (ψ := (1038926839/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_15_12)
    (by simpa only [half_16_12_φ1] using half_16_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_12_total1, half_16_12_total2, half_16_12_total3, half_16_12_total4, half_16_12_total5, half_16_12_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_17_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1055354307/10000000000 : ℝ)

private theorem half_17_12_total1 : total half_17_12_φ1=(1055354307/10000000000 : ℝ) := by
  norm_num [half_17_12_φ1,total,emptyPhi,Fin.snoc]

private theorem half_17_12_bounds1 : ∀ l,0≤half_17_12_φ1 l ∧ half_17_12_φ1 l≤1 ∧
    0≤shiftExponents 9 half_17_12_φ1 l :=
  alternate_bounds_snoc emptyPhi (1055354307/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_17_12_φ2 : Fin 2 → ℝ := Fin.snoc half_17_12_φ1 (259022199/2500000000 : ℝ)

private theorem half_17_12_total2 : total half_17_12_φ2=(2091443103/10000000000 : ℝ) := by
  change total (Fin.snoc half_17_12_φ1 (259022199/2500000000 : ℝ))=(2091443103/10000000000 : ℝ)
  rw [alternate_total_snoc,half_17_12_total1]
  norm_num

private theorem half_17_12_bounds2 : ∀ l,0≤half_17_12_φ2 l ∧ half_17_12_φ2 l≤1 ∧
    0≤shiftExponents 9 half_17_12_φ2 l :=
  alternate_bounds_snoc half_17_12_φ1 (259022199/2500000000 : ℝ) half_17_12_bounds1 (by norm_num)

private def half_17_12_φ3 : Fin 3 → ℝ := Fin.snoc half_17_12_φ2 (988569611/10000000000 : ℝ)

private theorem half_17_12_total3 : total half_17_12_φ3=(1540006357/5000000000 : ℝ) := by
  change total (Fin.snoc half_17_12_φ2 (988569611/10000000000 : ℝ))=(1540006357/5000000000 : ℝ)
  rw [alternate_total_snoc,half_17_12_total2]
  norm_num

private theorem half_17_12_bounds3 : ∀ l,0≤half_17_12_φ3 l ∧ half_17_12_φ3 l≤1 ∧
    0≤shiftExponents 9 half_17_12_φ3 l :=
  alternate_bounds_snoc half_17_12_φ2 (988569611/10000000000 : ℝ) half_17_12_bounds2 (by norm_num)

private def half_17_12_φ4 : Fin 4 → ℝ := Fin.snoc half_17_12_φ3 (86499841/1000000000 : ℝ)

private theorem half_17_12_total4 : total half_17_12_φ4=(986252781/2500000000 : ℝ) := by
  change total (Fin.snoc half_17_12_φ3 (86499841/1000000000 : ℝ))=(986252781/2500000000 : ℝ)
  rw [alternate_total_snoc,half_17_12_total3]
  norm_num

private theorem half_17_12_bounds4 : ∀ l,0≤half_17_12_φ4 l ∧ half_17_12_φ4 l≤1 ∧
    0≤shiftExponents 9 half_17_12_φ4 l :=
  alternate_bounds_snoc half_17_12_φ3 (86499841/1000000000 : ℝ) half_17_12_bounds3 (by norm_num)

private def half_17_12_φ5 : Fin 5 → ℝ := Fin.snoc half_17_12_φ4 (756873609/10000000000 : ℝ)

private theorem half_17_12_total5 : total half_17_12_φ5=(4701884733/10000000000 : ℝ) := by
  change total (Fin.snoc half_17_12_φ4 (756873609/10000000000 : ℝ))=(4701884733/10000000000 : ℝ)
  rw [alternate_total_snoc,half_17_12_total4]
  norm_num

private theorem half_17_12_bounds5 : ∀ l,0≤half_17_12_φ5 l ∧ half_17_12_φ5 l≤1 ∧
    0≤shiftExponents 9 half_17_12_φ5 l :=
  alternate_bounds_snoc half_17_12_φ4 (756873609/10000000000 : ℝ) half_17_12_bounds4 (by norm_num)

private def half_17_12_φ6 : Fin 6 → ℝ := Fin.snoc half_17_12_φ5 (662264407/10000000000 : ℝ)

private theorem half_17_12_total6 : total half_17_12_φ6=(268207457/500000000 : ℝ) := by
  change total (Fin.snoc half_17_12_φ5 (662264407/10000000000 : ℝ))=(268207457/500000000 : ℝ)
  rw [alternate_total_snoc,half_17_12_total5]
  norm_num

private theorem half_17_12_bounds6 : ∀ l,0≤half_17_12_φ6 l ∧ half_17_12_φ6 l≤1 ∧
    0≤shiftExponents 9 half_17_12_φ6 l :=
  alternate_bounds_snoc half_17_12_φ5 (662264407/10000000000 : ℝ) half_17_12_bounds5 (by norm_num)

private theorem half_17_12_prefix : PrefixCondition 9 half_17_12_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, half_17_12_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_17_12_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_17_12_φ6) (445377629/62500000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_17_12_φ6
    (fun i => (half_17_12_bounds6 i).1) (fun i => (half_17_12_bounds6 i).2.1)
    (fun i => (half_17_12_bounds6 i).2.2) half_17_12_prefix
  convert h using 1 <;> norm_num [half_17_12_total1, half_17_12_total2, half_17_12_total3, half_17_12_total4, half_17_12_total5, half_17_12_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_17_12_hx6 : SourcePowerBound
    (powerBoxCross 9 11 64 half_17_12_φ6) (90607390019/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 11) (r := 2) (v := 14) (w := 15) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_17_12_φ6 (by norm_num [half_17_12_total1, half_17_12_total2, half_17_12_total3, half_17_12_total4, half_17_12_total5, half_17_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_17_12_total1, half_17_12_total2, half_17_12_total3, half_17_12_total4, half_17_12_total5, half_17_12_total6, parameterExponent, curveLoss, dyadicExponent]) half_17_12_hF2
    (half_14_12) (half_15_12)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_12_total1, half_17_12_total2, half_17_12_total3, half_17_12_total4, half_17_12_total5, half_17_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_12_hx5 : SourcePowerBound
    (powerBoxCross 9 12 32 half_17_12_φ5) (1654022711/156250000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 12) (u := 10) (t := 13)
    (D := 32) (ψ := (662264407/10000000000 : ℝ)) half_17_12_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_12_bounds5 l).1) (fun l => (half_17_12_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_12_total1, half_17_12_total2, half_17_12_total3, half_17_12_total4, half_17_12_total5, half_17_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_12) (half_13_12)
    (by simpa only [half_17_12_φ6, show (2:ℝ)*32=64 by norm_num] using half_17_12_hx6)
  exact h.weaken (by norm_num [half_17_12_total1, half_17_12_total2, half_17_12_total3, half_17_12_total4, half_17_12_total5, half_17_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_12_hx4 : SourcePowerBound
    (powerBoxCross 9 13 16 half_17_12_φ4) (125511594703/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (756873609/10000000000 : ℝ)) half_17_12_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_12_bounds4 l).1) (fun l => (half_17_12_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_12_total1, half_17_12_total2, half_17_12_total3, half_17_12_total4, half_17_12_total5, half_17_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_12) (half_14_12)
    (by simpa only [half_17_12_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_12_hx5)
  exact h.weaken (by norm_num [half_17_12_total1, half_17_12_total2, half_17_12_total3, half_17_12_total4, half_17_12_total5, half_17_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_12_hx3 : SourcePowerBound
    (powerBoxCross 9 14 8 half_17_12_φ3) (75407658653/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (86499841/1000000000 : ℝ)) half_17_12_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_12_bounds3 l).1) (fun l => (half_17_12_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_12_total1, half_17_12_total2, half_17_12_total3, half_17_12_total4, half_17_12_total5, half_17_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_12) (half_15_12)
    (by simpa only [half_17_12_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_12_hx4)
  exact h.weaken (by norm_num [half_17_12_total1, half_17_12_total2, half_17_12_total3, half_17_12_total4, half_17_12_total5, half_17_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_12_hx2 : SourcePowerBound
    (powerBoxCross 9 15 4 half_17_12_φ2) (22879039843/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (988569611/10000000000 : ℝ)) half_17_12_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_12_bounds2 l).1) (fun l => (half_17_12_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_12_total1, half_17_12_total2, half_17_12_total3, half_17_12_total4, half_17_12_total5, half_17_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_12) (half_16_12)
    (by simpa only [half_17_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_12_hx3)
  exact h.weaken (by norm_num [half_17_12_total1, half_17_12_total2, half_17_12_total3, half_17_12_total4, half_17_12_total5, half_17_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_12_hx1 : SourcePowerBound
    (powerBoxCross 9 16 2 half_17_12_φ1) (44123870381/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (259022199/2500000000 : ℝ)) half_17_12_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_12_bounds1 l).1) (fun l => (half_17_12_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_12_total1, half_17_12_total2, half_17_12_total3, half_17_12_total4, half_17_12_total5, half_17_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_12) (half_17_11)
    (by simpa only [half_17_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_12_hx2)
  exact h.weaken (by norm_num [half_17_12_total1, half_17_12_total2, half_17_12_total3, half_17_12_total4, half_17_12_total5, half_17_12_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_17_12 : AdmissibleExponent 9 34 (126667667711/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 15) (ψ := (1055354307/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_16_12)
    (by simpa only [half_17_12_φ1] using half_17_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_12_total1, half_17_12_total2, half_17_12_total3, half_17_12_total4, half_17_12_total5, half_17_12_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_18_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (534123617/5000000000 : ℝ)

private theorem half_18_12_total1 : total half_18_12_φ1=(534123617/5000000000 : ℝ) := by
  norm_num [half_18_12_φ1,total,emptyPhi,Fin.snoc]

private theorem half_18_12_bounds1 : ∀ l,0≤half_18_12_φ1 l ∧ half_18_12_φ1 l≤1 ∧
    0≤shiftExponents 9 half_18_12_φ1 l :=
  alternate_bounds_snoc emptyPhi (534123617/5000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_18_12_φ2 : Fin 2 → ℝ := Fin.snoc half_18_12_φ1 (131762599/1250000000 : ℝ)

private theorem half_18_12_total2 : total half_18_12_φ2=(1061174013/5000000000 : ℝ) := by
  change total (Fin.snoc half_18_12_φ1 (131762599/1250000000 : ℝ))=(1061174013/5000000000 : ℝ)
  rw [alternate_total_snoc,half_18_12_total1]
  norm_num

private theorem half_18_12_bounds2 : ∀ l,0≤half_18_12_φ2 l ∧ half_18_12_φ2 l≤1 ∧
    0≤shiftExponents 9 half_18_12_φ2 l :=
  alternate_bounds_snoc half_18_12_φ1 (131762599/1250000000 : ℝ) half_18_12_bounds1 (by norm_num)

private def half_18_12_φ3 : Fin 3 → ℝ := Fin.snoc half_18_12_φ2 (15386039/156250000 : ℝ)

private theorem half_18_12_total3 : total half_18_12_φ3=(1553527261/5000000000 : ℝ) := by
  change total (Fin.snoc half_18_12_φ2 (15386039/156250000 : ℝ))=(1553527261/5000000000 : ℝ)
  rw [alternate_total_snoc,half_18_12_total2]
  norm_num

private theorem half_18_12_bounds3 : ∀ l,0≤half_18_12_φ3 l ∧ half_18_12_φ3 l≤1 ∧
    0≤shiftExponents 9 half_18_12_φ3 l :=
  alternate_bounds_snoc half_18_12_φ2 (15386039/156250000 : ℝ) half_18_12_bounds2 (by norm_num)

private def half_18_12_φ4 : Fin 4 → ℝ := Fin.snoc half_18_12_φ3 (107702273/1250000000 : ℝ)

private theorem half_18_12_total4 : total half_18_12_φ4=(1984336353/5000000000 : ℝ) := by
  change total (Fin.snoc half_18_12_φ3 (107702273/1250000000 : ℝ))=(1984336353/5000000000 : ℝ)
  rw [alternate_total_snoc,half_18_12_total3]
  norm_num

private theorem half_18_12_bounds4 : ∀ l,0≤half_18_12_φ4 l ∧ half_18_12_φ4 l≤1 ∧
    0≤shiftExponents 9 half_18_12_φ4 l :=
  alternate_bounds_snoc half_18_12_φ3 (107702273/1250000000 : ℝ) half_18_12_bounds3 (by norm_num)

private def half_18_12_φ5 : Fin 5 → ℝ := Fin.snoc half_18_12_φ4 (753915911/10000000000 : ℝ)

private theorem half_18_12_total5 : total half_18_12_φ5=(4722588617/10000000000 : ℝ) := by
  change total (Fin.snoc half_18_12_φ4 (753915911/10000000000 : ℝ))=(4722588617/10000000000 : ℝ)
  rw [alternate_total_snoc,half_18_12_total4]
  norm_num

private theorem half_18_12_bounds5 : ∀ l,0≤half_18_12_φ5 l ∧ half_18_12_φ5 l≤1 ∧
    0≤shiftExponents 9 half_18_12_φ5 l :=
  alternate_bounds_snoc half_18_12_φ4 (753915911/10000000000 : ℝ) half_18_12_bounds4 (by norm_num)

private def half_18_12_φ6 : Fin 6 → ℝ := Fin.snoc half_18_12_φ5 (329838211/5000000000 : ℝ)

private theorem half_18_12_total6 : total half_18_12_φ6=(5382265039/10000000000 : ℝ) := by
  change total (Fin.snoc half_18_12_φ5 (329838211/5000000000 : ℝ))=(5382265039/10000000000 : ℝ)
  rw [alternate_total_snoc,half_18_12_total5]
  norm_num

private theorem half_18_12_bounds6 : ∀ l,0≤half_18_12_φ6 l ∧ half_18_12_φ6 l≤1 ∧
    0≤shiftExponents 9 half_18_12_φ6 l :=
  alternate_bounds_snoc half_18_12_φ5 (329838211/5000000000 : ℝ) half_18_12_bounds5 (by norm_num)

private theorem half_18_12_prefix : PrefixCondition 9 half_18_12_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_18_12_φ1, half_18_12_φ2, half_18_12_φ3, half_18_12_φ4, half_18_12_φ5, half_18_12_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_18_12_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_18_12_φ6) (8853204883/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_18_12_φ6
    (fun i => (half_18_12_bounds6 i).1) (fun i => (half_18_12_bounds6 i).2.1)
    (fun i => (half_18_12_bounds6 i).2.2) half_18_12_prefix
  convert h using 1 <;> norm_num [half_18_12_total1, half_18_12_total2, half_18_12_total3, half_18_12_total4, half_18_12_total5, half_18_12_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_18_12_hx6 : SourcePowerBound
    (powerBoxCross 9 12 64 half_18_12_φ6) (98848052889/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 12) (r := 2) (v := 0) (w := 16) (D := 64)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_18_12_φ6 (by norm_num [half_18_12_total1, half_18_12_total2, half_18_12_total3, half_18_12_total4, half_18_12_total5, half_18_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_18_12_total1, half_18_12_total2, half_18_12_total3, half_18_12_total4, half_18_12_total5, half_18_12_total6, parameterExponent, curveLoss, dyadicExponent]) half_18_12_hF2
    (admissibleExponent_zero 9) (half_16_12)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_18_12_total1, half_18_12_total2, half_18_12_total3, half_18_12_total4, half_18_12_total5, half_18_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_12_hx5 : SourcePowerBound
    (powerBoxCross 9 13 32 half_18_12_φ5) (57558733189/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 13) (u := 11) (t := 14)
    (D := 32) (ψ := (329838211/5000000000 : ℝ)) half_18_12_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_12_bounds5 l).1) (fun l => (half_18_12_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_12_total1, half_18_12_total2, half_18_12_total3, half_18_12_total4, half_18_12_total5, half_18_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_12) (half_14_12)
    (by simpa only [half_18_12_φ6, show (2:ℝ)*32=64 by norm_num] using half_18_12_hx6)
  exact h.weaken (by norm_num [half_18_12_total1, half_18_12_total2, half_18_12_total3, half_18_12_total4, half_18_12_total5, half_18_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_12_hx4 : SourcePowerBound
    (powerBoxCross 9 14 16 half_18_12_φ4) (17012403451/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 14) (u := 12) (t := 15)
    (D := 16) (ψ := (753915911/10000000000 : ℝ)) half_18_12_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_12_bounds4 l).1) (fun l => (half_18_12_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_12_total1, half_18_12_total2, half_18_12_total3, half_18_12_total4, half_18_12_total5, half_18_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_12) (half_15_12)
    (by simpa only [half_18_12_φ5, show (2:ℝ)*16=32 by norm_num] using half_18_12_hx5)
  exact h.weaken (by norm_num [half_18_12_total1, half_18_12_total2, half_18_12_total3, half_18_12_total4, half_18_12_total5, half_18_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_12_hx3 : SourcePowerBound
    (powerBoxCross 9 15 8 half_18_12_φ3) (20375076253/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 15) (u := 13) (t := 16)
    (D := 8) (ψ := (107702273/1250000000 : ℝ)) half_18_12_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_12_bounds3 l).1) (fun l => (half_18_12_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_12_total1, half_18_12_total2, half_18_12_total3, half_18_12_total4, half_18_12_total5, half_18_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_12) (half_16_12)
    (by simpa only [half_18_12_φ4, show (2:ℝ)*8=16 by norm_num] using half_18_12_hx4)
  exact h.weaken (by norm_num [half_18_12_total1, half_18_12_total2, half_18_12_total3, half_18_12_total4, half_18_12_total5, half_18_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_12_hx2 : SourcePowerBound
    (powerBoxCross 9 16 4 half_18_12_φ2) (197073537359/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 16) (u := 14) (t := 17)
    (D := 4) (ψ := (15386039/156250000 : ℝ)) half_18_12_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_12_bounds2 l).1) (fun l => (half_18_12_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_12_total1, half_18_12_total2, half_18_12_total3, half_18_12_total4, half_18_12_total5, half_18_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_12) (half_17_12)
    (by simpa only [half_18_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_18_12_hx3)
  exact h.weaken (by norm_num [half_18_12_total1, half_18_12_total2, half_18_12_total3, half_18_12_total4, half_18_12_total5, half_18_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_12_hx1 : SourcePowerBound
    (powerBoxCross 9 17 2 half_18_12_φ1) (237341105529/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 17) (u := 15) (t := 18)
    (D := 2) (ψ := (131762599/1250000000 : ℝ)) half_18_12_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_12_bounds1 l).1) (fun l => (half_18_12_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_12_total1, half_18_12_total2, half_18_12_total3, half_18_12_total4, half_18_12_total5, half_18_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_12) (half_18_11)
    (by simpa only [half_18_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_18_12_hx2)
  exact h.weaken (by norm_num [half_18_12_total1, half_18_12_total2, half_18_12_total3, half_18_12_total4, half_18_12_total5, half_18_12_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_18_12 : AdmissibleExponent 9 36 (272593264251/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 16) (ψ := (534123617/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_17_12)
    (by simpa only [half_18_12_φ1] using half_18_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_18_12_total1, half_18_12_total2, half_18_12_total3, half_18_12_total4, half_18_12_total5, half_18_12_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_19_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1078522243/10000000000 : ℝ)

private theorem half_19_12_total1 : total half_19_12_φ1=(1078522243/10000000000 : ℝ) := by
  norm_num [half_19_12_φ1,total,emptyPhi,Fin.snoc]

private theorem half_19_12_bounds1 : ∀ l,0≤half_19_12_φ1 l ∧ half_19_12_φ1 l≤1 ∧
    0≤shiftExponents 9 half_19_12_φ1 l :=
  alternate_bounds_snoc emptyPhi (1078522243/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_19_12_φ2 : Fin 2 → ℝ := Fin.snoc half_19_12_φ1 (106824061/1000000000 : ℝ)

private theorem half_19_12_total2 : total half_19_12_φ2=(2146762853/10000000000 : ℝ) := by
  change total (Fin.snoc half_19_12_φ1 (106824061/1000000000 : ℝ))=(2146762853/10000000000 : ℝ)
  rw [alternate_total_snoc,half_19_12_total1]
  norm_num

private theorem half_19_12_bounds2 : ∀ l,0≤half_19_12_φ2 l ∧ half_19_12_φ2 l≤1 ∧
    0≤shiftExponents 9 half_19_12_φ2 l :=
  alternate_bounds_snoc half_19_12_φ1 (106824061/1000000000 : ℝ) half_19_12_bounds1 (by norm_num)

private def half_19_12_φ3 : Fin 3 → ℝ := Fin.snoc half_19_12_φ2 (981654643/10000000000 : ℝ)

private theorem half_19_12_total3 : total half_19_12_φ3=(391052187/1250000000 : ℝ) := by
  change total (Fin.snoc half_19_12_φ2 (981654643/10000000000 : ℝ))=(391052187/1250000000 : ℝ)
  rw [alternate_total_snoc,half_19_12_total2]
  norm_num

private theorem half_19_12_bounds3 : ∀ l,0≤half_19_12_φ3 l ∧ half_19_12_φ3 l≤1 ∧
    0≤shiftExponents 9 half_19_12_φ3 l :=
  alternate_bounds_snoc half_19_12_φ2 (981654643/10000000000 : ℝ) half_19_12_bounds2 (by norm_num)

private def half_19_12_φ4 : Fin 4 → ℝ := Fin.snoc half_19_12_φ3 (214736953/2500000000 : ℝ)

private theorem half_19_12_total4 : total half_19_12_φ4=(996841327/2500000000 : ℝ) := by
  change total (Fin.snoc half_19_12_φ3 (214736953/2500000000 : ℝ))=(996841327/2500000000 : ℝ)
  rw [alternate_total_snoc,half_19_12_total3]
  norm_num

private theorem half_19_12_bounds4 : ∀ l,0≤half_19_12_φ4 l ∧ half_19_12_φ4 l≤1 ∧
    0≤shiftExponents 9 half_19_12_φ4 l :=
  alternate_bounds_snoc half_19_12_φ3 (214736953/2500000000 : ℝ) half_19_12_bounds3 (by norm_num)

private def half_19_12_φ5 : Fin 5 → ℝ := Fin.snoc half_19_12_φ4 (93947417/1250000000 : ℝ)

private theorem half_19_12_total5 : total half_19_12_φ5=(1184736161/2500000000 : ℝ) := by
  change total (Fin.snoc half_19_12_φ4 (93947417/1250000000 : ℝ))=(1184736161/2500000000 : ℝ)
  rw [alternate_total_snoc,half_19_12_total4]
  norm_num

private theorem half_19_12_bounds5 : ∀ l,0≤half_19_12_φ5 l ∧ half_19_12_φ5 l≤1 ∧
    0≤shiftExponents 9 half_19_12_φ5 l :=
  alternate_bounds_snoc half_19_12_φ4 (93947417/1250000000 : ℝ) half_19_12_bounds4 (by norm_num)

private def half_19_12_φ6 : Fin 6 → ℝ := Fin.snoc half_19_12_φ5 (657631919/10000000000 : ℝ)

private theorem half_19_12_total6 : total half_19_12_φ6=(5396576563/10000000000 : ℝ) := by
  change total (Fin.snoc half_19_12_φ5 (657631919/10000000000 : ℝ))=(5396576563/10000000000 : ℝ)
  rw [alternate_total_snoc,half_19_12_total5]
  norm_num

private theorem half_19_12_bounds6 : ∀ l,0≤half_19_12_φ6 l ∧ half_19_12_φ6 l≤1 ∧
    0≤shiftExponents 9 half_19_12_φ6 l :=
  alternate_bounds_snoc half_19_12_φ5 (657631919/10000000000 : ℝ) half_19_12_bounds5 (by norm_num)

private theorem half_19_12_prefix : PrefixCondition 9 half_19_12_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_19_12_φ1, half_19_12_φ2, half_19_12_φ3, half_19_12_φ4, half_19_12_φ5, half_19_12_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_19_12_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_19_12_φ6) (8810270311/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_19_12_φ6
    (fun i => (half_19_12_bounds6 i).1) (fun i => (half_19_12_bounds6 i).2.1)
    (fun i => (half_19_12_bounds6 i).2.2) half_19_12_prefix
  convert h using 1 <;> norm_num [half_19_12_total1, half_19_12_total2, half_19_12_total3, half_19_12_total4, half_19_12_total5, half_19_12_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_19_12_hx6 : SourcePowerBound
    (powerBoxCross 9 13 64 half_19_12_φ6) (107302587183/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 13) (r := 2) (v := 17) (w := 18) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_19_12_φ6 (by norm_num [half_19_12_total1, half_19_12_total2, half_19_12_total3, half_19_12_total4, half_19_12_total5, half_19_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_19_12_total1, half_19_12_total2, half_19_12_total3, half_19_12_total4, half_19_12_total5, half_19_12_total6, parameterExponent, curveLoss, dyadicExponent]) half_19_12_hF2
    (half_17_12) (half_18_12)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_19_12_total1, half_19_12_total2, half_19_12_total3, half_19_12_total4, half_19_12_total5, half_19_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_12_hx5 : SourcePowerBound
    (powerBoxCross 9 14 32 half_19_12_φ5) (124606999639/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 14) (u := 12) (t := 15)
    (D := 32) (ψ := (657631919/10000000000 : ℝ)) half_19_12_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_12_bounds5 l).1) (fun l => (half_19_12_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_12_total1, half_19_12_total2, half_19_12_total3, half_19_12_total4, half_19_12_total5, half_19_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_12) (half_15_12)
    (by simpa only [half_19_12_φ6, show (2:ℝ)*32=64 by norm_num] using half_19_12_hx6)
  exact h.weaken (by norm_num [half_19_12_total1, half_19_12_total2, half_19_12_total3, half_19_12_total4, half_19_12_total5, half_19_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_12_hx4 : SourcePowerBound
    (powerBoxCross 9 15 16 half_19_12_φ4) (73467666489/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 15) (u := 13) (t := 16)
    (D := 16) (ψ := (93947417/1250000000 : ℝ)) half_19_12_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_12_bounds4 l).1) (fun l => (half_19_12_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_12_total1, half_19_12_total2, half_19_12_total3, half_19_12_total4, half_19_12_total5, half_19_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_12) (half_16_12)
    (by simpa only [half_19_12_φ5, show (2:ℝ)*16=32 by norm_num] using half_19_12_hx5)
  exact h.weaken (by norm_num [half_19_12_total1, half_19_12_total2, half_19_12_total3, half_19_12_total4, half_19_12_total5, half_19_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_12_hx3 : SourcePowerBound
    (powerBoxCross 9 16 8 half_19_12_φ3) (87724736353/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 16) (u := 14) (t := 17)
    (D := 8) (ψ := (214736953/2500000000 : ℝ)) half_19_12_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_12_bounds3 l).1) (fun l => (half_19_12_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_12_total1, half_19_12_total2, half_19_12_total3, half_19_12_total4, half_19_12_total5, half_19_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_12) (half_17_12)
    (by simpa only [half_19_12_φ4, show (2:ℝ)*8=16 by norm_num] using half_19_12_hx4)
  exact h.weaken (by norm_num [half_19_12_total1, half_19_12_total2, half_19_12_total3, half_19_12_total4, half_19_12_total5, half_19_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_12_hx2 : SourcePowerBound
    (powerBoxCross 9 17 4 half_19_12_φ2) (4227806187/200000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 17) (u := 15) (t := 18)
    (D := 4) (ψ := (981654643/10000000000 : ℝ)) half_19_12_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_12_bounds2 l).1) (fun l => (half_19_12_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_12_total1, half_19_12_total2, half_19_12_total3, half_19_12_total4, half_19_12_total5, half_19_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_12) (half_18_12)
    (by simpa only [half_19_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_19_12_hx3)
  exact h.weaken (by norm_num [half_19_12_total1, half_19_12_total2, half_19_12_total3, half_19_12_total4, half_19_12_total5, half_19_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_12_hx1 : SourcePowerBound
    (powerBoxCross 9 18 2 half_19_12_φ1) (127135998311/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 18) (u := 16) (t := 19)
    (D := 2) (ψ := (106824061/1000000000 : ℝ)) half_19_12_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_12_bounds1 l).1) (fun l => (half_19_12_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_12_total1, half_19_12_total2, half_19_12_total3, half_19_12_total4, half_19_12_total5, half_19_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_12) (half_19_11)
    (by simpa only [half_19_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_19_12_hx2)
  exact h.weaken (by norm_num [half_19_12_total1, half_19_12_total2, half_19_12_total3, half_19_12_total4, half_19_12_total5, half_19_12_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_19_12 : AdmissibleExponent 9 38 (292020275127/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 17) (ψ := (1078522243/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_18_12)
    (by simpa only [half_19_12_φ1] using half_19_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_19_12_total1, half_19_12_total2, half_19_12_total3, half_19_12_total4, half_19_12_total5, half_19_12_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_20_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (16977093/156250000 : ℝ)

private theorem half_20_12_total1 : total half_20_12_φ1=(16977093/156250000 : ℝ) := by
  norm_num [half_20_12_φ1,total,emptyPhi,Fin.snoc]

private theorem half_20_12_bounds1 : ∀ l,0≤half_20_12_φ1 l ∧ half_20_12_φ1 l≤1 ∧
    0≤shiftExponents 9 half_20_12_φ1 l :=
  alternate_bounds_snoc emptyPhi (16977093/156250000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_20_12_φ2 : Fin 2 → ℝ := Fin.snoc half_20_12_φ1 (134920921/1250000000 : ℝ)

private theorem half_20_12_total2 : total half_20_12_φ2=(54147533/250000000 : ℝ) := by
  change total (Fin.snoc half_20_12_φ1 (134920921/1250000000 : ℝ))=(54147533/250000000 : ℝ)
  rw [alternate_total_snoc,half_20_12_total1]
  norm_num

private theorem half_20_12_bounds2 : ∀ l,0≤half_20_12_φ2 l ∧ half_20_12_φ2 l≤1 ∧
    0≤shiftExponents 9 half_20_12_φ2 l :=
  alternate_bounds_snoc half_20_12_φ1 (134920921/1250000000 : ℝ) half_20_12_bounds1 (by norm_num)

private def half_20_12_φ3 : Fin 3 → ℝ := Fin.snoc half_20_12_φ2 (489631167/5000000000 : ℝ)

private theorem half_20_12_total3 : total half_20_12_φ3=(1572581827/5000000000 : ℝ) := by
  change total (Fin.snoc half_20_12_φ2 (489631167/5000000000 : ℝ))=(1572581827/5000000000 : ℝ)
  rw [alternate_total_snoc,half_20_12_total2]
  norm_num

private theorem half_20_12_bounds3 : ∀ l,0≤half_20_12_φ3 l ∧ half_20_12_φ3 l≤1 ∧
    0≤shiftExponents 9 half_20_12_φ3 l :=
  alternate_bounds_snoc half_20_12_φ2 (489631167/5000000000 : ℝ) half_20_12_bounds2 (by norm_num)

private def half_20_12_φ4 : Fin 4 → ℝ := Fin.snoc half_20_12_φ3 (856854543/10000000000 : ℝ)

private theorem half_20_12_total4 : total half_20_12_φ4=(4002018197/10000000000 : ℝ) := by
  change total (Fin.snoc half_20_12_φ3 (856854543/10000000000 : ℝ))=(4002018197/10000000000 : ℝ)
  rw [alternate_total_snoc,half_20_12_total3]
  norm_num

private theorem half_20_12_bounds4 : ∀ l,0≤half_20_12_φ4 l ∧ half_20_12_φ4 l≤1 ∧
    0≤shiftExponents 9 half_20_12_φ4 l :=
  alternate_bounds_snoc half_20_12_φ3 (856854543/10000000000 : ℝ) half_20_12_bounds3 (by norm_num)

private def half_20_12_φ5 : Fin 5 → ℝ := Fin.snoc half_20_12_φ4 (29989909/400000000 : ℝ)

private theorem half_20_12_total5 : total half_20_12_φ5=(2375882961/5000000000 : ℝ) := by
  change total (Fin.snoc half_20_12_φ4 (29989909/400000000 : ℝ))=(2375882961/5000000000 : ℝ)
  rw [alternate_total_snoc,half_20_12_total4]
  norm_num

private theorem half_20_12_bounds5 : ∀ l,0≤half_20_12_φ5 l ∧ half_20_12_φ5 l≤1 ∧
    0≤shiftExponents 9 half_20_12_φ5 l :=
  alternate_bounds_snoc half_20_12_φ4 (29989909/400000000 : ℝ) half_20_12_bounds4 (by norm_num)

private def half_20_12_φ6 : Fin 6 → ℝ := Fin.snoc half_20_12_φ5 (656029259/10000000000 : ℝ)

private theorem half_20_12_total6 : total half_20_12_φ6=(5407795181/10000000000 : ℝ) := by
  change total (Fin.snoc half_20_12_φ5 (656029259/10000000000 : ℝ))=(5407795181/10000000000 : ℝ)
  rw [alternate_total_snoc,half_20_12_total5]
  norm_num

private theorem half_20_12_bounds6 : ∀ l,0≤half_20_12_φ6 l ∧ half_20_12_φ6 l≤1 ∧
    0≤shiftExponents 9 half_20_12_φ6 l :=
  alternate_bounds_snoc half_20_12_φ5 (656029259/10000000000 : ℝ) half_20_12_bounds5 (by norm_num)

private theorem half_20_12_prefix : PrefixCondition 9 half_20_12_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_20_12_φ1, half_20_12_φ2, half_20_12_φ3, half_20_12_φ4, half_20_12_φ5, half_20_12_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_20_12_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_20_12_φ6) (8776614457/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_20_12_φ6
    (fun i => (half_20_12_bounds6 i).1) (fun i => (half_20_12_bounds6 i).2.1)
    (fun i => (half_20_12_bounds6 i).2.2) half_20_12_prefix
  convert h using 1 <;> norm_num [half_20_12_total1, half_20_12_total2, half_20_12_total3, half_20_12_total4, half_20_12_total5, half_20_12_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_20_12_hx6 : SourcePowerBound
    (powerBoxCross 9 14 64 half_20_12_φ6) (14487397149/1250000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 14) (r := 2) (v := 18) (w := 19) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_20_12_φ6 (by norm_num [half_20_12_total1, half_20_12_total2, half_20_12_total3, half_20_12_total4, half_20_12_total5, half_20_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_20_12_total1, half_20_12_total2, half_20_12_total3, half_20_12_total4, half_20_12_total5, half_20_12_total6, parameterExponent, curveLoss, dyadicExponent]) half_20_12_hF2
    (half_18_12) (half_19_12)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_20_12_total1, half_20_12_total2, half_20_12_total3, half_20_12_total4, half_20_12_total5, half_20_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_12_hx5 : SourcePowerBound
    (powerBoxCross 9 15 32 half_20_12_φ5) (134279326811/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 15) (u := 13) (t := 16)
    (D := 32) (ψ := (656029259/10000000000 : ℝ)) half_20_12_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_12_bounds5 l).1) (fun l => (half_20_12_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_12_total1, half_20_12_total2, half_20_12_total3, half_20_12_total4, half_20_12_total5, half_20_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_12) (half_16_12)
    (by simpa only [half_20_12_φ6, show (2:ℝ)*32=64 by norm_num] using half_20_12_hx6)
  exact h.weaken (by norm_num [half_20_12_total1, half_20_12_total2, half_20_12_total3, half_20_12_total4, half_20_12_total5, half_20_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_12_hx4 : SourcePowerBound
    (powerBoxCross 9 16 16 half_20_12_φ4) (78988984613/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 16) (u := 14) (t := 17)
    (D := 16) (ψ := (29989909/400000000 : ℝ)) half_20_12_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_12_bounds4 l).1) (fun l => (half_20_12_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_12_total1, half_20_12_total2, half_20_12_total3, half_20_12_total4, half_20_12_total5, half_20_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_12) (half_17_12)
    (by simpa only [half_20_12_φ5, show (2:ℝ)*16=32 by norm_num] using half_20_12_hx5)
  exact h.weaken (by norm_num [half_20_12_total1, half_20_12_total2, half_20_12_total3, half_20_12_total4, half_20_12_total5, half_20_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_12_hx3 : SourcePowerBound
    (powerBoxCross 9 17 8 half_20_12_φ3) (188118686187/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 17) (u := 15) (t := 18)
    (D := 8) (ψ := (856854543/10000000000 : ℝ)) half_20_12_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_12_bounds3 l).1) (fun l => (half_20_12_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_12_total1, half_20_12_total2, half_20_12_total3, half_20_12_total4, half_20_12_total5, half_20_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_12) (half_18_12)
    (by simpa only [half_20_12_φ4, show (2:ℝ)*8=16 by norm_num] using half_20_12_hx4)
  exact h.weaken (by norm_num [half_20_12_total1, half_20_12_total2, half_20_12_total3, half_20_12_total4, half_20_12_total5, half_20_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_12_hx2 : SourcePowerBound
    (powerBoxCross 9 18 4 half_20_12_φ2) (5648483723/250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 18) (u := 16) (t := 19)
    (D := 4) (ψ := (489631167/5000000000 : ℝ)) half_20_12_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_12_bounds2 l).1) (fun l => (half_20_12_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_12_total1, half_20_12_total2, half_20_12_total3, half_20_12_total4, half_20_12_total5, half_20_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_12) (half_19_12)
    (by simpa only [half_20_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_20_12_hx3)
  exact h.weaken (by norm_num [half_20_12_total1, half_20_12_total2, half_20_12_total3, half_20_12_total4, half_20_12_total5, half_20_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_12_hx1 : SourcePowerBound
    (powerBoxCross 9 19 2 half_20_12_φ1) (271377814723/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 19) (u := 17) (t := 20)
    (D := 2) (ψ := (134920921/1250000000 : ℝ)) half_20_12_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_12_bounds1 l).1) (fun l => (half_20_12_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_12_total1, half_20_12_total2, half_20_12_total3, half_20_12_total4, half_20_12_total5, half_20_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_12) (half_20_11)
    (by simpa only [half_20_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_20_12_hx2)
  exact h.weaken (by norm_num [half_20_12_total1, half_20_12_total2, half_20_12_total3, half_20_12_total4, half_20_12_total5, half_20_12_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_20_12 : AdmissibleExponent 9 40 (311579570947/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 18) (ψ := (16977093/156250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_19_12)
    (by simpa only [half_20_12_φ1] using half_20_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_20_12_total1, half_20_12_total2, half_20_12_total3, half_20_12_total4, half_20_12_total5, half_20_12_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_21_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (546393479/5000000000 : ℝ)

private theorem half_21_12_total1 : total half_21_12_φ1=(546393479/5000000000 : ℝ) := by
  norm_num [half_21_12_φ1,total,emptyPhi,Fin.snoc]

private theorem half_21_12_bounds1 : ∀ l,0≤half_21_12_φ1 l ∧ half_21_12_φ1 l≤1 ∧
    0≤shiftExponents 9 half_21_12_φ1 l :=
  alternate_bounds_snoc emptyPhi (546393479/5000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_21_12_φ2 : Fin 2 → ℝ := Fin.snoc half_21_12_φ1 (108802479/1000000000 : ℝ)

private theorem half_21_12_total2 : total half_21_12_φ2=(545202937/2500000000 : ℝ) := by
  change total (Fin.snoc half_21_12_φ1 (108802479/1000000000 : ℝ))=(545202937/2500000000 : ℝ)
  rw [alternate_total_snoc,half_21_12_total1]
  norm_num

private theorem half_21_12_bounds2 : ∀ l,0≤half_21_12_φ2 l ∧ half_21_12_φ2 l≤1 ∧
    0≤shiftExponents 9 half_21_12_φ2 l :=
  alternate_bounds_snoc half_21_12_φ1 (108802479/1000000000 : ℝ) half_21_12_bounds1 (by norm_num)

private def half_21_12_φ3 : Fin 3 → ℝ := Fin.snoc half_21_12_φ2 (977398531/10000000000 : ℝ)

private theorem half_21_12_total3 : total half_21_12_φ3=(3158210279/10000000000 : ℝ) := by
  change total (Fin.snoc half_21_12_φ2 (977398531/10000000000 : ℝ))=(3158210279/10000000000 : ℝ)
  rw [alternate_total_snoc,half_21_12_total2]
  norm_num

private theorem half_21_12_bounds3 : ∀ l,0≤half_21_12_φ3 l ∧ half_21_12_φ3 l≤1 ∧
    0≤shiftExponents 9 half_21_12_φ3 l :=
  alternate_bounds_snoc half_21_12_φ2 (977398531/10000000000 : ℝ) half_21_12_bounds2 (by norm_num)

private def half_21_12_φ4 : Fin 4 → ℝ := Fin.snoc half_21_12_φ3 (427611857/5000000000 : ℝ)

private theorem half_21_12_total4 : total half_21_12_φ4=(4013433993/10000000000 : ℝ) := by
  change total (Fin.snoc half_21_12_φ3 (427611857/5000000000 : ℝ))=(4013433993/10000000000 : ℝ)
  rw [alternate_total_snoc,half_21_12_total3]
  norm_num

private theorem half_21_12_bounds4 : ∀ l,0≤half_21_12_φ4 l ∧ half_21_12_φ4 l≤1 ∧
    0≤shiftExponents 9 half_21_12_φ4 l :=
  alternate_bounds_snoc half_21_12_φ3 (427611857/5000000000 : ℝ) half_21_12_bounds3 (by norm_num)

private def half_21_12_φ5 : Fin 5 → ℝ := Fin.snoc half_21_12_φ4 (2993283/40000000 : ℝ)

private theorem half_21_12_total5 : total half_21_12_φ5=(4761754743/10000000000 : ℝ) := by
  change total (Fin.snoc half_21_12_φ4 (2993283/40000000 : ℝ))=(4761754743/10000000000 : ℝ)
  rw [alternate_total_snoc,half_21_12_total4]
  norm_num

private theorem half_21_12_bounds5 : ∀ l,0≤half_21_12_φ5 l ∧ half_21_12_φ5 l≤1 ∧
    0≤shiftExponents 9 half_21_12_φ5 l :=
  alternate_bounds_snoc half_21_12_φ4 (2993283/40000000 : ℝ) half_21_12_bounds4 (by norm_num)

private def half_21_12_φ6 : Fin 6 → ℝ := Fin.snoc half_21_12_φ5 (40923791/625000000 : ℝ)

private theorem half_21_12_total6 : total half_21_12_φ6=(5416535399/10000000000 : ℝ) := by
  change total (Fin.snoc half_21_12_φ5 (40923791/625000000 : ℝ))=(5416535399/10000000000 : ℝ)
  rw [alternate_total_snoc,half_21_12_total5]
  norm_num

private theorem half_21_12_bounds6 : ∀ l,0≤half_21_12_φ6 l ∧ half_21_12_φ6 l≤1 ∧
    0≤shiftExponents 9 half_21_12_φ6 l :=
  alternate_bounds_snoc half_21_12_φ5 (40923791/625000000 : ℝ) half_21_12_bounds5 (by norm_num)

private theorem half_21_12_prefix : PrefixCondition 9 half_21_12_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_21_12_φ1, half_21_12_φ2, half_21_12_φ3, half_21_12_φ4, half_21_12_φ5, half_21_12_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_21_12_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_21_12_φ6) (8750393803/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_21_12_φ6
    (fun i => (half_21_12_bounds6 i).1) (fun i => (half_21_12_bounds6 i).2.1)
    (fun i => (half_21_12_bounds6 i).2.2) half_21_12_prefix
  convert h using 1 <;> norm_num [half_21_12_total1, half_21_12_total2, half_21_12_total3, half_21_12_total4, half_21_12_total5, half_21_12_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_21_12_hx6 : SourcePowerBound
    (powerBoxCross 9 15 64 half_21_12_φ6) (31152333161/2500000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 15) (r := 2) (v := 0) (w := 20) (D := 64)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_21_12_φ6 (by norm_num [half_21_12_total1, half_21_12_total2, half_21_12_total3, half_21_12_total4, half_21_12_total5, half_21_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_21_12_total1, half_21_12_total2, half_21_12_total3, half_21_12_total4, half_21_12_total5, half_21_12_total6, parameterExponent, curveLoss, dyadicExponent]) half_21_12_hF2
    (admissibleExponent_zero 9) (half_20_12)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_21_12_total1, half_21_12_total2, half_21_12_total3, half_21_12_total4, half_21_12_total5, half_21_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_12_hx5 : SourcePowerBound
    (powerBoxCross 9 16 32 half_21_12_φ5) (144103597823/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 16) (u := 14) (t := 17)
    (D := 32) (ψ := (40923791/625000000 : ℝ)) half_21_12_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_12_bounds5 l).1) (fun l => (half_21_12_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_12_total1, half_21_12_total2, half_21_12_total3, half_21_12_total4, half_21_12_total5, half_21_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_12) (half_17_12)
    (by simpa only [half_21_12_φ6, show (2:ℝ)*32=64 by norm_num] using half_21_12_hx6)
  exact h.weaken (by norm_num [half_21_12_total1, half_21_12_total2, half_21_12_total3, half_21_12_total4, half_21_12_total5, half_21_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_12_hx4 : SourcePowerBound
    (powerBoxCross 9 17 16 half_21_12_φ4) (2114898913/125000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 17) (u := 15) (t := 18)
    (D := 16) (ψ := (2993283/40000000 : ℝ)) half_21_12_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_12_bounds4 l).1) (fun l => (half_21_12_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_12_total1, half_21_12_total2, half_21_12_total3, half_21_12_total4, half_21_12_total5, half_21_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_12) (half_18_12)
    (by simpa only [half_21_12_φ5, show (2:ℝ)*16=32 by norm_num] using half_21_12_hx5)
  exact h.weaken (by norm_num [half_21_12_total1, half_21_12_total2, half_21_12_total3, half_21_12_total4, half_21_12_total5, half_21_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_12_hx3 : SourcePowerBound
    (powerBoxCross 9 18 8 half_21_12_φ3) (5024284313/250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 18) (u := 16) (t := 19)
    (D := 8) (ψ := (427611857/5000000000 : ℝ)) half_21_12_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_12_bounds3 l).1) (fun l => (half_21_12_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_12_total1, half_21_12_total2, half_21_12_total3, half_21_12_total4, half_21_12_total5, half_21_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_12) (half_19_12)
    (by simpa only [half_21_12_φ4, show (2:ℝ)*8=16 by norm_num] using half_21_12_hx4)
  exact h.weaken (by norm_num [half_21_12_total1, half_21_12_total2, half_21_12_total3, half_21_12_total4, half_21_12_total5, half_21_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_12_hx2 : SourcePowerBound
    (powerBoxCross 9 19 4 half_21_12_φ2) (240681879597/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 19) (u := 17) (t := 20)
    (D := 4) (ψ := (977398531/10000000000 : ℝ)) half_21_12_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_12_bounds2 l).1) (fun l => (half_21_12_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_12_total1, half_21_12_total2, half_21_12_total3, half_21_12_total4, half_21_12_total5, half_21_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_12) (half_20_12)
    (by simpa only [half_21_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_21_12_hx3)
  exact h.weaken (by norm_num [half_21_12_total1, half_21_12_total2, half_21_12_total3, half_21_12_total4, half_21_12_total5, half_21_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_12_hx1 : SourcePowerBound
    (powerBoxCross 9 20 2 half_21_12_φ1) (144311674379/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 20) (u := 18) (t := 21)
    (D := 2) (ψ := (108802479/1000000000 : ℝ)) half_21_12_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_12_bounds1 l).1) (fun l => (half_21_12_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_12_total1, half_21_12_total2, half_21_12_total3, half_21_12_total4, half_21_12_total5, half_21_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_19_12) (half_21_11)
    (by simpa only [half_21_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_21_12_hx2)
  exact h.weaken (by norm_num [half_21_12_total1, half_21_12_total2, half_21_12_total3, half_21_12_total4, half_21_12_total5, half_21_12_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_21_12 : AdmissibleExponent 9 42 (8281051003/250000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 19) (ψ := (546393479/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_20_12)
    (by simpa only [half_21_12_φ1] using half_21_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_21_12_total1, half_21_12_total2, half_21_12_total3, half_21_12_total4, half_21_12_total5, half_21_12_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_22_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1097708887/10000000000 : ℝ)

private theorem half_22_12_total1 : total half_22_12_φ1=(1097708887/10000000000 : ℝ) := by
  norm_num [half_22_12_φ1,total,emptyPhi,Fin.snoc]

private theorem half_22_12_bounds1 : ∀ l,0≤half_22_12_φ1 l ∧ half_22_12_φ1 l≤1 ∧
    0≤shiftExponents 9 half_22_12_φ1 l :=
  alternate_bounds_snoc emptyPhi (1097708887/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_22_12_φ2 : Fin 2 → ℝ := Fin.snoc half_22_12_φ1 (218966323/2000000000 : ℝ)

private theorem half_22_12_total2 : total half_22_12_φ2=(1096270251/5000000000 : ℝ) := by
  change total (Fin.snoc half_22_12_φ1 (218966323/2000000000 : ℝ))=(1096270251/5000000000 : ℝ)
  rw [alternate_total_snoc,half_22_12_total1]
  norm_num

private theorem half_22_12_bounds2 : ∀ l,0≤half_22_12_φ2 l ∧ half_22_12_φ2 l≤1 ∧
    0≤shiftExponents 9 half_22_12_φ2 l :=
  alternate_bounds_snoc half_22_12_φ1 (218966323/2000000000 : ℝ) half_22_12_bounds1 (by norm_num)

private def half_22_12_φ3 : Fin 3 → ℝ := Fin.snoc half_22_12_φ2 (975932437/10000000000 : ℝ)

private theorem half_22_12_total3 : total half_22_12_φ3=(3168472939/10000000000 : ℝ) := by
  change total (Fin.snoc half_22_12_φ2 (975932437/10000000000 : ℝ))=(3168472939/10000000000 : ℝ)
  rw [alternate_total_snoc,half_22_12_total2]
  norm_num

private theorem half_22_12_bounds3 : ∀ l,0≤half_22_12_φ3 l ∧ half_22_12_φ3 l≤1 ∧
    0≤shiftExponents 9 half_22_12_φ3 l :=
  alternate_bounds_snoc half_22_12_φ2 (975932437/10000000000 : ℝ) half_22_12_bounds2 (by norm_num)

private def half_22_12_φ4 : Fin 4 → ℝ := Fin.snoc half_22_12_φ3 (426970441/5000000000 : ℝ)

private theorem half_22_12_total4 : total half_22_12_φ4=(4022413821/10000000000 : ℝ) := by
  change total (Fin.snoc half_22_12_φ3 (426970441/5000000000 : ℝ))=(4022413821/10000000000 : ℝ)
  rw [alternate_total_snoc,half_22_12_total3]
  norm_num

private theorem half_22_12_bounds4 : ∀ l,0≤half_22_12_φ4 l ∧ half_22_12_φ4 l≤1 ∧
    0≤shiftExponents 9 half_22_12_φ4 l :=
  alternate_bounds_snoc half_22_12_φ3 (426970441/5000000000 : ℝ) half_22_12_bounds3 (by norm_num)

private def half_22_12_φ5 : Fin 5 → ℝ := Fin.snoc half_22_12_φ4 (11674973/156250000 : ℝ)

private theorem half_22_12_total5 : total half_22_12_φ5=(4769612093/10000000000 : ℝ) := by
  change total (Fin.snoc half_22_12_φ4 (11674973/156250000 : ℝ))=(4769612093/10000000000 : ℝ)
  rw [alternate_total_snoc,half_22_12_total4]
  norm_num

private theorem half_22_12_bounds5 : ∀ l,0≤half_22_12_φ5 l ∧ half_22_12_φ5 l≤1 ∧
    0≤shiftExponents 9 half_22_12_φ5 l :=
  alternate_bounds_snoc half_22_12_φ4 (11674973/156250000 : ℝ) half_22_12_bounds4 (by norm_num)

private def half_22_12_φ6 : Fin 6 → ℝ := Fin.snoc half_22_12_φ5 (81724811/1250000000 : ℝ)

private theorem half_22_12_total6 : total half_22_12_φ6=(5423410581/10000000000 : ℝ) := by
  change total (Fin.snoc half_22_12_φ5 (81724811/1250000000 : ℝ))=(5423410581/10000000000 : ℝ)
  rw [alternate_total_snoc,half_22_12_total5]
  norm_num

private theorem half_22_12_bounds6 : ∀ l,0≤half_22_12_φ6 l ∧ half_22_12_φ6 l≤1 ∧
    0≤shiftExponents 9 half_22_12_φ6 l :=
  alternate_bounds_snoc half_22_12_φ5 (81724811/1250000000 : ℝ) half_22_12_bounds5 (by norm_num)

private theorem half_22_12_prefix : PrefixCondition 9 half_22_12_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_22_12_φ1, half_22_12_φ2, half_22_12_φ3, half_22_12_φ4, half_22_12_φ5, half_22_12_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_22_12_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_22_12_φ6) (8729768257/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_22_12_φ6
    (fun i => (half_22_12_bounds6 i).1) (fun i => (half_22_12_bounds6 i).2.1)
    (fun i => (half_22_12_bounds6 i).2.2) half_22_12_prefix
  convert h using 1 <;> norm_num [half_22_12_total1, half_22_12_total2, half_22_12_total3, half_22_12_total4, half_22_12_total5, half_22_12_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_22_12_hx6 : SourcePowerBound
    (powerBoxCross 9 16 64 half_22_12_φ6) (133416175927/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 16) (r := 2) (v := 21) (w := 22) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_22_12_φ6 (by norm_num [half_22_12_total1, half_22_12_total2, half_22_12_total3, half_22_12_total4, half_22_12_total5, half_22_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_22_12_total1, half_22_12_total2, half_22_12_total3, half_22_12_total4, half_22_12_total5, half_22_12_total6, parameterExponent, curveLoss, dyadicExponent]) half_22_12_hF2
    (half_21_12) (half_22_11)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_22_12_total1, half_22_12_total2, half_22_12_total3, half_22_12_total4, half_22_12_total5, half_22_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_12_hx5 : SourcePowerBound
    (powerBoxCross 9 17 32 half_22_12_φ5) (154051941799/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 17) (u := 15) (t := 18)
    (D := 32) (ψ := (81724811/1250000000 : ℝ)) half_22_12_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_12_bounds5 l).1) (fun l => (half_22_12_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_12_total1, half_22_12_total2, half_22_12_total3, half_22_12_total4, half_22_12_total5, half_22_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_12) (half_18_12)
    (by simpa only [half_22_12_φ6, show (2:ℝ)*32=64 by norm_num] using half_22_12_hx6)
  exact h.weaken (by norm_num [half_22_12_total1, half_22_12_total2, half_22_12_total3, half_22_12_total4, half_22_12_total5, half_22_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_12_hx4 : SourcePowerBound
    (powerBoxCross 9 18 16 half_22_12_φ4) (180543905133/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 18) (u := 16) (t := 19)
    (D := 16) (ψ := (11674973/156250000 : ℝ)) half_22_12_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_12_bounds4 l).1) (fun l => (half_22_12_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_12_total1, half_22_12_total2, half_22_12_total3, half_22_12_total4, half_22_12_total5, half_22_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_12) (half_19_12)
    (by simpa only [half_22_12_φ5, show (2:ℝ)*16=32 by norm_num] using half_22_12_hx5)
  exact h.weaken (by norm_num [half_22_12_total1, half_22_12_total2, half_22_12_total3, half_22_12_total4, half_22_12_total5, half_22_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_12_hx3 : SourcePowerBound
    (powerBoxCross 9 19 8 half_22_12_φ3) (8558809591/400000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 19) (u := 17) (t := 20)
    (D := 8) (ψ := (426970441/5000000000 : ℝ)) half_22_12_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_12_bounds3 l).1) (fun l => (half_22_12_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_12_total1, half_22_12_total2, half_22_12_total3, half_22_12_total4, half_22_12_total5, half_22_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_12) (half_20_12)
    (by simpa only [half_22_12_φ4, show (2:ℝ)*8=16 by norm_num] using half_22_12_hx4)
  exact h.weaken (by norm_num [half_22_12_total1, half_22_12_total2, half_22_12_total3, half_22_12_total4, half_22_12_total5, half_22_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_12_hx2 : SourcePowerBound
    (powerBoxCross 9 20 4 half_22_12_φ2) (127788824289/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 20) (u := 18) (t := 21)
    (D := 4) (ψ := (975932437/10000000000 : ℝ)) half_22_12_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_12_bounds2 l).1) (fun l => (half_22_12_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_12_total1, half_22_12_total2, half_22_12_total3, half_22_12_total4, half_22_12_total5, half_22_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_19_12) (half_21_12)
    (by simpa only [half_22_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_22_12_hx3)
  exact h.weaken (by norm_num [half_22_12_total1, half_22_12_total2, half_22_12_total3, half_22_12_total4, half_22_12_total5, half_22_12_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_12_hx1 : SourcePowerBound
    (powerBoxCross 9 21 2 half_22_12_φ1) (38247376987/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 21) (u := 19) (t := 22)
    (D := 2) (ψ := (218966323/2000000000 : ℝ)) half_22_12_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_12_bounds1 l).1) (fun l => (half_22_12_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_12_total1, half_22_12_total2, half_22_12_total3, half_22_12_total4, half_22_12_total5, half_22_12_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_20_12) (half_22_11)
    (by simpa only [half_22_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_22_12_hx2)
  exact h.weaken (by norm_num [half_22_12_total1, half_22_12_total2, half_22_12_total3, half_22_12_total4, half_22_12_total5, half_22_12_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_22_12 : AdmissibleExponent 9 44 (350985080263/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 20) (ψ := (1097708887/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_21_12)
    (by simpa only [half_22_12_φ1] using half_22_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_22_12_total1, half_22_12_total2, half_22_12_total3, half_22_12_total4, half_22_12_total5, half_22_12_total6, parameterExponent, curveLoss, dyadicExponent])

end Waring.SeedCompletionAlternate9Seeds
