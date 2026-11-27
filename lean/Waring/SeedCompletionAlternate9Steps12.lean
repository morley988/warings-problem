import Waring.SeedCompletionAlternate9Steps11

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionAlternate9Seeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges SeedCompletionDivisorPowerScales
open PolicyCompletionSharpResidualSource

private def half_12_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (236729291/2500000000 : ℝ)

private theorem half_12_11_total1 : total half_12_11_φ1=(236729291/2500000000 : ℝ) := by
  norm_num [half_12_11_φ1,total,emptyPhi,Fin.snoc]

private theorem half_12_11_bounds1 : ∀ l,0≤half_12_11_φ1 l ∧ half_12_11_φ1 l≤1 ∧
    0≤shiftExponents 9 half_12_11_φ1 l :=
  alternate_bounds_snoc emptyPhi (236729291/2500000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_12_11_φ2 : Fin 2 → ℝ := Fin.snoc half_12_11_φ1 (90320169/1000000000 : ℝ)

private theorem half_12_11_total2 : total half_12_11_φ2=(925059427/5000000000 : ℝ) := by
  change total (Fin.snoc half_12_11_φ1 (90320169/1000000000 : ℝ))=(925059427/5000000000 : ℝ)
  rw [alternate_total_snoc,half_12_11_total1]
  norm_num

private theorem half_12_11_bounds2 : ∀ l,0≤half_12_11_φ2 l ∧ half_12_11_φ2 l≤1 ∧
    0≤shiftExponents 9 half_12_11_φ2 l :=
  alternate_bounds_snoc half_12_11_φ1 (90320169/1000000000 : ℝ) half_12_11_bounds1 (by norm_num)

private def half_12_11_φ3 : Fin 3 → ℝ := Fin.snoc half_12_11_φ2 (420365941/5000000000 : ℝ)

private theorem half_12_11_total3 : total half_12_11_φ3=(168178171/625000000 : ℝ) := by
  change total (Fin.snoc half_12_11_φ2 (420365941/5000000000 : ℝ))=(168178171/625000000 : ℝ)
  rw [alternate_total_snoc,half_12_11_total2]
  norm_num

private theorem half_12_11_bounds3 : ∀ l,0≤half_12_11_φ3 l ∧ half_12_11_φ3 l≤1 ∧
    0≤shiftExponents 9 half_12_11_φ3 l :=
  alternate_bounds_snoc half_12_11_φ2 (420365941/5000000000 : ℝ) half_12_11_bounds2 (by norm_num)

private def half_12_11_φ4 : Fin 4 → ℝ := Fin.snoc half_12_11_φ3 (72796749/1000000000 : ℝ)

private theorem half_12_11_total4 : total half_12_11_φ4=(1709409113/5000000000 : ℝ) := by
  change total (Fin.snoc half_12_11_φ3 (72796749/1000000000 : ℝ))=(1709409113/5000000000 : ℝ)
  rw [alternate_total_snoc,half_12_11_total3]
  norm_num

private theorem half_12_11_bounds4 : ∀ l,0≤half_12_11_φ4 l ∧ half_12_11_φ4 l≤1 ∧
    0≤shiftExponents 9 half_12_11_φ4 l :=
  alternate_bounds_snoc half_12_11_φ3 (72796749/1000000000 : ℝ) half_12_11_bounds3 (by norm_num)

private def half_12_11_φ5 : Fin 5 → ℝ := Fin.snoc half_12_11_φ4 (225162359/5000000000 : ℝ)

private theorem half_12_11_total5 : total half_12_11_φ5=(120910717/312500000 : ℝ) := by
  change total (Fin.snoc half_12_11_φ4 (225162359/5000000000 : ℝ))=(120910717/312500000 : ℝ)
  rw [alternate_total_snoc,half_12_11_total4]
  norm_num

private theorem half_12_11_bounds5 : ∀ l,0≤half_12_11_φ5 l ∧ half_12_11_φ5 l≤1 ∧
    0≤shiftExponents 9 half_12_11_φ5 l :=
  alternate_bounds_snoc half_12_11_φ4 (225162359/5000000000 : ℝ) half_12_11_bounds4 (by norm_num)

private theorem half_12_11_prefix : PrefixCondition 9 half_12_11_φ5 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_12_11_φ1, half_12_11_φ2, half_12_11_φ3, half_12_11_φ4, half_12_11_φ5, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_12_11_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 32 half_12_11_φ5) (301330349/39062500 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_12_11_φ5
    (fun i => (half_12_11_bounds5 i).1) (fun i => (half_12_11_bounds5 i).2.1)
    (fun i => (half_12_11_bounds5 i).2.2) half_12_11_prefix
  convert h using 1 <;> norm_num [half_12_11_total1, half_12_11_total2, half_12_11_total3, half_12_11_total4, half_12_11_total5, parameterExponent, curveLoss, dyadicExponent]

private theorem half_12_11_hx5 : SourcePowerBound
    (powerBoxCross 9 7 32 half_12_11_φ5) (36489095737/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 7) (r := 2) (v := 9) (w := 10) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_12_11_φ5 (by norm_num [half_12_11_total1, half_12_11_total2, half_12_11_total3, half_12_11_total4, half_12_11_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_12_11_total1, half_12_11_total2, half_12_11_total3, half_12_11_total4, half_12_11_total5, parameterExponent, curveLoss, dyadicExponent]) half_12_11_hF2
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_10_11)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_11_total1, half_12_11_total2, half_12_11_total3, half_12_11_total4, half_12_11_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_11_hx4 : SourcePowerBound
    (powerBoxCross 9 8 16 half_12_11_φ4) (41203175471/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 8) (u := 6) (t := 9)
    (D := 16) (ψ := (225162359/5000000000 : ℝ)) half_12_11_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_11_bounds4 l).1) (fun l => (half_12_11_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_11_total1, half_12_11_total2, half_12_11_total3, half_12_11_total4, half_12_11_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_7) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_12_11_φ5, show (2:ℝ)*16=32 by norm_num] using half_12_11_hx5)
  exact h.weaken (by norm_num [half_12_11_total1, half_12_11_total2, half_12_11_total3, half_12_11_total4, half_12_11_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_11_hx3 : SourcePowerBound
    (powerBoxCross 9 9 8 half_12_11_φ3) (6092624723/625000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (72796749/1000000000 : ℝ)) half_12_11_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_11_bounds3 l).1) (fun l => (half_12_11_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_11_total1, half_12_11_total2, half_12_11_total3, half_12_11_total4, half_12_11_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_11)
    (by simpa only [half_12_11_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_11_hx4)
  exact h.weaken (by norm_num [half_12_11_total1, half_12_11_total2, half_12_11_total3, half_12_11_total4, half_12_11_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_11_hx2 : SourcePowerBound
    (powerBoxCross 9 10 4 half_12_11_φ2) (117209056221/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (420365941/5000000000 : ℝ)) half_12_11_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_11_bounds2 l).1) (fun l => (half_12_11_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_11_total1, half_12_11_total2, half_12_11_total3, half_12_11_total4, half_12_11_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_11)
    (by simpa only [half_12_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_11_hx3)
  exact h.weaken (by norm_num [half_12_11_total1, half_12_11_total2, half_12_11_total3, half_12_11_total4, half_12_11_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_11_hx1 : SourcePowerBound
    (powerBoxCross 9 11 2 half_12_11_φ1) (17675901931/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (90320169/1000000000 : ℝ)) half_12_11_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_11_bounds1 l).1) (fun l => (half_12_11_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_11_total1, half_12_11_total2, half_12_11_total3, half_12_11_total4, half_12_11_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_11) (half_12_10)
    (by simpa only [half_12_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_11_hx2)
  exact h.weaken (by norm_num [half_12_11_total1, half_12_11_total2, half_12_11_total3, half_12_11_total4, half_12_11_total5, parameterExponent, curveLoss, dyadicExponent])

theorem half_12_11 : AdmissibleExponent 9 24 (40323118973/2500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 10) (ψ := (236729291/2500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_11_11)
    (by simpa only [half_12_11_φ1] using half_12_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_11_total1, half_12_11_total2, half_12_11_total3, half_12_11_total4, half_12_11_total5, parameterExponent, curveLoss, dyadicExponent])

private def half_13_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (974240181/10000000000 : ℝ)

private theorem half_13_11_total1 : total half_13_11_φ1=(974240181/10000000000 : ℝ) := by
  norm_num [half_13_11_φ1,total,emptyPhi,Fin.snoc]

private theorem half_13_11_bounds1 : ∀ l,0≤half_13_11_φ1 l ∧ half_13_11_φ1 l≤1 ∧
    0≤shiftExponents 9 half_13_11_φ1 l :=
  alternate_bounds_snoc emptyPhi (974240181/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_13_11_φ2 : Fin 2 → ℝ := Fin.snoc half_13_11_φ1 (93560581/1000000000 : ℝ)

private theorem half_13_11_total2 : total half_13_11_φ2=(1909845991/10000000000 : ℝ) := by
  change total (Fin.snoc half_13_11_φ1 (93560581/1000000000 : ℝ))=(1909845991/10000000000 : ℝ)
  rw [alternate_total_snoc,half_13_11_total1]
  norm_num

private theorem half_13_11_bounds2 : ∀ l,0≤half_13_11_φ2 l ∧ half_13_11_φ2 l≤1 ∧
    0≤shiftExponents 9 half_13_11_φ2 l :=
  alternate_bounds_snoc half_13_11_φ1 (93560581/1000000000 : ℝ) half_13_11_bounds1 (by norm_num)

private def half_13_11_φ3 : Fin 3 → ℝ := Fin.snoc half_13_11_φ2 (55151181/625000000 : ℝ)

private theorem half_13_11_total3 : total half_13_11_φ3=(2792264887/10000000000 : ℝ) := by
  change total (Fin.snoc half_13_11_φ2 (55151181/625000000 : ℝ))=(2792264887/10000000000 : ℝ)
  rw [alternate_total_snoc,half_13_11_total2]
  norm_num

private theorem half_13_11_bounds3 : ∀ l,0≤half_13_11_φ3 l ∧ half_13_11_φ3 l≤1 ∧
    0≤shiftExponents 9 half_13_11_φ3 l :=
  alternate_bounds_snoc half_13_11_φ2 (55151181/625000000 : ℝ) half_13_11_bounds2 (by norm_num)

private def half_13_11_φ4 : Fin 4 → ℝ := Fin.snoc half_13_11_φ3 (794479203/10000000000 : ℝ)

private theorem half_13_11_total4 : total half_13_11_φ4=(358674409/1000000000 : ℝ) := by
  change total (Fin.snoc half_13_11_φ3 (794479203/10000000000 : ℝ))=(358674409/1000000000 : ℝ)
  rw [alternate_total_snoc,half_13_11_total3]
  norm_num

private theorem half_13_11_bounds4 : ∀ l,0≤half_13_11_φ4 l ∧ half_13_11_φ4 l≤1 ∧
    0≤shiftExponents 9 half_13_11_φ4 l :=
  alternate_bounds_snoc half_13_11_φ3 (794479203/10000000000 : ℝ) half_13_11_bounds3 (by norm_num)

private def half_13_11_φ5 : Fin 5 → ℝ := Fin.snoc half_13_11_φ4 (303471879/5000000000 : ℝ)

private theorem half_13_11_total5 : total half_13_11_φ5=(524210981/1250000000 : ℝ) := by
  change total (Fin.snoc half_13_11_φ4 (303471879/5000000000 : ℝ))=(524210981/1250000000 : ℝ)
  rw [alternate_total_snoc,half_13_11_total4]
  norm_num

private theorem half_13_11_bounds5 : ∀ l,0≤half_13_11_φ5 l ∧ half_13_11_φ5 l≤1 ∧
    0≤shiftExponents 9 half_13_11_φ5 l :=
  alternate_bounds_snoc half_13_11_φ4 (303471879/5000000000 : ℝ) half_13_11_bounds4 (by norm_num)

private theorem half_13_11_prefix : PrefixCondition 9 half_13_11_φ5 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_13_11_φ1, half_13_11_φ2, half_13_11_φ3, half_13_11_φ4, half_13_11_φ5, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_13_11_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 32 half_13_11_φ5) (1083617057/156250000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_13_11_φ5
    (fun i => (half_13_11_bounds5 i).1) (fun i => (half_13_11_bounds5 i).2.1)
    (fun i => (half_13_11_bounds5 i).2.2) half_13_11_prefix
  convert h using 1 <;> norm_num [half_13_11_total1, half_13_11_total2, half_13_11_total3, half_13_11_total4, half_13_11_total5, parameterExponent, curveLoss, dyadicExponent]

private theorem half_13_11_hx5 : SourcePowerBound
    (powerBoxCross 9 8 32 half_13_11_φ5) (77676389089/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 8) (r := 2) (v := 10) (w := 11) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_13_11_φ5 (by norm_num [half_13_11_total1, half_13_11_total2, half_13_11_total3, half_13_11_total4, half_13_11_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_13_11_total1, half_13_11_total2, half_13_11_total3, half_13_11_total4, half_13_11_total5, parameterExponent, curveLoss, dyadicExponent]) half_13_11_hF2
    (half_10_11) (half_11_11)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_11_total1, half_13_11_total2, half_13_11_total3, half_13_11_total4, half_13_11_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_11_hx4 : SourcePowerBound
    (powerBoxCross 9 9 16 half_13_11_φ4) (89916080621/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (303471879/5000000000 : ℝ)) half_13_11_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_11_bounds4 l).1) (fun l => (half_13_11_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_11_total1, half_13_11_total2, half_13_11_total3, half_13_11_total4, half_13_11_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_11)
    (by simpa only [half_13_11_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_11_hx5)
  exact h.weaken (by norm_num [half_13_11_total1, half_13_11_total2, half_13_11_total3, half_13_11_total4, half_13_11_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_11_hx3 : SourcePowerBound
    (powerBoxCross 9 10 8 half_13_11_φ3) (107475925011/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (794479203/10000000000 : ℝ)) half_13_11_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_11_bounds3 l).1) (fun l => (half_13_11_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_11_total1, half_13_11_total2, half_13_11_total3, half_13_11_total4, half_13_11_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_11)
    (by simpa only [half_13_11_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_11_hx4)
  exact h.weaken (by norm_num [half_13_11_total1, half_13_11_total2, half_13_11_total3, half_13_11_total4, half_13_11_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_11_hx2 : SourcePowerBound
    (powerBoxCross 9 11 4 half_13_11_φ2) (129725606577/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (55151181/625000000 : ℝ)) half_13_11_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_11_bounds2 l).1) (fun l => (half_13_11_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_11_total1, half_13_11_total2, half_13_11_total3, half_13_11_total4, half_13_11_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_11) (half_12_11)
    (by simpa only [half_13_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_11_hx3)
  exact h.weaken (by norm_num [half_13_11_total1, half_13_11_total2, half_13_11_total3, half_13_11_total4, half_13_11_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_11_hx1 : SourcePowerBound
    (powerBoxCross 9 12 2 half_13_11_φ1) (156552954987/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (93560581/1000000000 : ℝ)) half_13_11_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_11_bounds1 l).1) (fun l => (half_13_11_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_11_total1, half_13_11_total2, half_13_11_total3, half_13_11_total4, half_13_11_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_11) (half_13_10)
    (by simpa only [half_13_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_11_hx2)
  exact h.weaken (by norm_num [half_13_11_total1, half_13_11_total2, half_13_11_total3, half_13_11_total4, half_13_11_total5, parameterExponent, curveLoss, dyadicExponent])

theorem half_13_11 : AdmissibleExponent 9 26 (3579209583/200000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 11) (ψ := (974240181/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_12_11)
    (by simpa only [half_13_11_φ1] using half_13_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_11_total1, half_13_11_total2, half_13_11_total3, half_13_11_total4, half_13_11_total5, parameterExponent, curveLoss, dyadicExponent])

private def half_14_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (999198539/10000000000 : ℝ)

private theorem half_14_11_total1 : total half_14_11_φ1=(999198539/10000000000 : ℝ) := by
  norm_num [half_14_11_φ1,total,emptyPhi,Fin.snoc]

private theorem half_14_11_bounds1 : ∀ l,0≤half_14_11_φ1 l ∧ half_14_11_φ1 l≤1 ∧
    0≤shiftExponents 9 half_14_11_φ1 l :=
  alternate_bounds_snoc emptyPhi (999198539/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_14_11_φ2 : Fin 2 → ℝ := Fin.snoc half_14_11_φ1 (965227841/10000000000 : ℝ)

private theorem half_14_11_total2 : total half_14_11_φ2=(98221319/500000000 : ℝ) := by
  change total (Fin.snoc half_14_11_φ1 (965227841/10000000000 : ℝ))=(98221319/500000000 : ℝ)
  rw [alternate_total_snoc,half_14_11_total1]
  norm_num

private theorem half_14_11_bounds2 : ∀ l,0≤half_14_11_φ2 l ∧ half_14_11_φ2 l≤1 ∧
    0≤shiftExponents 9 half_14_11_φ2 l :=
  alternate_bounds_snoc half_14_11_φ1 (965227841/10000000000 : ℝ) half_14_11_bounds1 (by norm_num)

private def half_14_11_φ3 : Fin 3 → ℝ := Fin.snoc half_14_11_φ2 (920653973/10000000000 : ℝ)

private theorem half_14_11_total3 : total half_14_11_φ3=(2885080353/10000000000 : ℝ) := by
  change total (Fin.snoc half_14_11_φ2 (920653973/10000000000 : ℝ))=(2885080353/10000000000 : ℝ)
  rw [alternate_total_snoc,half_14_11_total2]
  norm_num

private theorem half_14_11_bounds3 : ∀ l,0≤half_14_11_φ3 l ∧ half_14_11_φ3 l≤1 ∧
    0≤shiftExponents 9 half_14_11_φ3 l :=
  alternate_bounds_snoc half_14_11_φ2 (920653973/10000000000 : ℝ) half_14_11_bounds2 (by norm_num)

private def half_14_11_φ4 : Fin 4 → ℝ := Fin.snoc half_14_11_φ3 (852630357/10000000000 : ℝ)

private theorem half_14_11_total4 : total half_14_11_φ4=(373771071/1000000000 : ℝ) := by
  change total (Fin.snoc half_14_11_φ3 (852630357/10000000000 : ℝ))=(373771071/1000000000 : ℝ)
  rw [alternate_total_snoc,half_14_11_total3]
  norm_num

private theorem half_14_11_bounds4 : ∀ l,0≤half_14_11_φ4 l ∧ half_14_11_φ4 l≤1 ∧
    0≤shiftExponents 9 half_14_11_φ4 l :=
  alternate_bounds_snoc half_14_11_φ3 (852630357/10000000000 : ℝ) half_14_11_bounds3 (by norm_num)

private def half_14_11_φ5 : Fin 5 → ℝ := Fin.snoc half_14_11_φ4 (181154183/2500000000 : ℝ)

private theorem half_14_11_total5 : total half_14_11_φ5=(2231163721/5000000000 : ℝ) := by
  change total (Fin.snoc half_14_11_φ4 (181154183/2500000000 : ℝ))=(2231163721/5000000000 : ℝ)
  rw [alternate_total_snoc,half_14_11_total4]
  norm_num

private theorem half_14_11_bounds5 : ∀ l,0≤half_14_11_φ5 l ∧ half_14_11_φ5 l≤1 ∧
    0≤shiftExponents 9 half_14_11_φ5 l :=
  alternate_bounds_snoc half_14_11_φ4 (181154183/2500000000 : ℝ) half_14_11_bounds4 (by norm_num)

private def half_14_11_φ6 : Fin 6 → ℝ := Fin.snoc half_14_11_φ5 (41926947/1000000000 : ℝ)

private theorem half_14_11_total6 : total half_14_11_φ6=(305099807/625000000 : ℝ) := by
  change total (Fin.snoc half_14_11_φ5 (41926947/1000000000 : ℝ))=(305099807/625000000 : ℝ)
  rw [alternate_total_snoc,half_14_11_total5]
  norm_num

private theorem half_14_11_bounds6 : ∀ l,0≤half_14_11_φ6 l ∧ half_14_11_φ6 l≤1 ∧
    0≤shiftExponents 9 half_14_11_φ6 l :=
  alternate_bounds_snoc half_14_11_φ5 (41926947/1000000000 : ℝ) half_14_11_bounds5 (by norm_num)

private theorem half_14_11_prefix : PrefixCondition 9 half_14_11_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_14_11_φ1, half_14_11_φ2, half_14_11_φ3, half_14_11_φ4, half_14_11_φ5, half_14_11_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_14_11_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_14_11_φ6) (647200579/78125000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_14_11_φ6
    (fun i => (half_14_11_bounds6 i).1) (fun i => (half_14_11_bounds6 i).2.1)
    (fun i => (half_14_11_bounds6 i).2.2) half_14_11_prefix
  convert h using 1 <;> norm_num [half_14_11_total1, half_14_11_total2, half_14_11_total3, half_14_11_total4, half_14_11_total5, half_14_11_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_14_11_hF1 : SourcePowerBound
    (paddedMoment 9 0 1 64 half_14_11_φ6) (241775193/78125000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_14_11_φ6
    (fun i => (half_14_11_bounds6 i).1) (fun i => (half_14_11_bounds6 i).2.1)
    (fun i => (half_14_11_bounds6 i).2.2) half_14_11_prefix
  convert h using 1 <;> norm_num [half_14_11_total1, half_14_11_total2, half_14_11_total3, half_14_11_total4, half_14_11_total5, half_14_11_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_14_11_hx6 : SourcePowerBound
    (powerBoxCross 9 8 64 half_14_11_φ6) (1477548391/200000000 : ℝ) := by
  have h := full_B_cross_power (k := 9) (s := 8) (r := 1) (v := 2) (t := 11) (D := 64)
    (a := (1/22 : ℝ)) (b := (5/22 : ℝ)) (c := (8/11 : ℝ))
    (by norm_num) half_14_11_φ6 (by norm_num [half_14_11_total1, half_14_11_total2, half_14_11_total3, half_14_11_total4, half_14_11_total5, half_14_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_14_11_total1, half_14_11_total2, half_14_11_total3, half_14_11_total4, half_14_11_total5, half_14_11_total6, parameterExponent, curveLoss, dyadicExponent]) half_14_11_hF1 half_14_11_hF2
    (half_11_11)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_11_total1, half_14_11_total2, half_14_11_total3, half_14_11_total4, half_14_11_total5, half_14_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_11_hx5 : SourcePowerBound
    (powerBoxCross 9 9 32 half_14_11_φ5) (82526461809/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 9) (u := 7) (t := 10)
    (D := 32) (ψ := (41926947/1000000000 : ℝ)) half_14_11_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_11_bounds5 l).1) (fun l => (half_14_11_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_11_total1, half_14_11_total2, half_14_11_total3, half_14_11_total4, half_14_11_total5, half_14_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_11)
    (by simpa only [half_14_11_φ6, show (2:ℝ)*32=64 by norm_num] using half_14_11_hx6)
  exact h.weaken (by norm_num [half_14_11_total1, half_14_11_total2, half_14_11_total3, half_14_11_total4, half_14_11_total5, half_14_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_11_hx4 : SourcePowerBound
    (powerBoxCross 9 10 16 half_14_11_φ4) (9759328351/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (181154183/2500000000 : ℝ)) half_14_11_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_11_bounds4 l).1) (fun l => (half_14_11_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_11_total1, half_14_11_total2, half_14_11_total3, half_14_11_total4, half_14_11_total5, half_14_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_11)
    (by simpa only [half_14_11_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_11_hx5)
  exact h.weaken (by norm_num [half_14_11_total1, half_14_11_total2, half_14_11_total3, half_14_11_total4, half_14_11_total5, half_14_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_11_hx3 : SourcePowerBound
    (powerBoxCross 9 11 8 half_14_11_φ3) (117735459017/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (852630357/10000000000 : ℝ)) half_14_11_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_11_bounds3 l).1) (fun l => (half_14_11_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_11_total1, half_14_11_total2, half_14_11_total3, half_14_11_total4, half_14_11_total5, half_14_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_11) (half_12_11)
    (by simpa only [half_14_11_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_11_hx4)
  exact h.weaken (by norm_num [half_14_11_total1, half_14_11_total2, half_14_11_total3, half_14_11_total4, half_14_11_total5, half_14_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_11_hx2 : SourcePowerBound
    (powerBoxCross 9 12 4 half_14_11_φ2) (14257939597/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (920653973/10000000000 : ℝ)) half_14_11_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_11_bounds2 l).1) (fun l => (half_14_11_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_11_total1, half_14_11_total2, half_14_11_total3, half_14_11_total4, half_14_11_total5, half_14_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_11) (half_13_11)
    (by simpa only [half_14_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_11_hx3)
  exact h.weaken (by norm_num [half_14_11_total1, half_14_11_total2, half_14_11_total3, half_14_11_total4, half_14_11_total5, half_14_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_11_hx1 : SourcePowerBound
    (powerBoxCross 9 13 2 half_14_11_φ1) (86038986383/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (965227841/10000000000 : ℝ)) half_14_11_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_11_bounds1 l).1) (fun l => (half_14_11_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_11_total1, half_14_11_total2, half_14_11_total3, half_14_11_total4, half_14_11_total5, half_14_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_11) (half_14_10)
    (by simpa only [half_14_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_11_hx2)
  exact h.weaken (by norm_num [half_14_11_total1, half_14_11_total2, half_14_11_total3, half_14_11_total4, half_14_11_total5, half_14_11_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_14_11 : AdmissibleExponent 9 28 (197057936241/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 12) (ψ := (999198539/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_13_11)
    (by simpa only [half_14_11_φ1] using half_14_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_11_total1, half_14_11_total2, half_14_11_total3, half_14_11_total4, half_14_11_total5, half_14_11_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_15_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1019510957/10000000000 : ℝ)

private theorem half_15_11_total1 : total half_15_11_φ1=(1019510957/10000000000 : ℝ) := by
  norm_num [half_15_11_φ1,total,emptyPhi,Fin.snoc]

private theorem half_15_11_bounds1 : ∀ l,0≤half_15_11_φ1 l ∧ half_15_11_φ1 l≤1 ∧
    0≤shiftExponents 9 half_15_11_φ1 l :=
  alternate_bounds_snoc emptyPhi (1019510957/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_15_11_φ2 : Fin 2 → ℝ := Fin.snoc half_15_11_φ1 (247596917/2500000000 : ℝ)

private theorem half_15_11_total2 : total half_15_11_φ2=(16079189/80000000 : ℝ) := by
  change total (Fin.snoc half_15_11_φ1 (247596917/2500000000 : ℝ))=(16079189/80000000 : ℝ)
  rw [alternate_total_snoc,half_15_11_total1]
  norm_num

private theorem half_15_11_bounds2 : ∀ l,0≤half_15_11_φ2 l ∧ half_15_11_φ2 l≤1 ∧
    0≤shiftExponents 9 half_15_11_φ2 l :=
  alternate_bounds_snoc half_15_11_φ1 (247596917/2500000000 : ℝ) half_15_11_bounds1 (by norm_num)

private def half_15_11_φ3 : Fin 3 → ℝ := Fin.snoc half_15_11_φ2 (950841759/10000000000 : ℝ)

private theorem half_15_11_total3 : total half_15_11_φ3=(92523137/312500000 : ℝ) := by
  change total (Fin.snoc half_15_11_φ2 (950841759/10000000000 : ℝ))=(92523137/312500000 : ℝ)
  rw [alternate_total_snoc,half_15_11_total2]
  norm_num

private theorem half_15_11_bounds3 : ∀ l,0≤half_15_11_φ3 l ∧ half_15_11_φ3 l≤1 ∧
    0≤shiftExponents 9 half_15_11_φ3 l :=
  alternate_bounds_snoc half_15_11_φ2 (950841759/10000000000 : ℝ) half_15_11_bounds2 (by norm_num)

private def half_15_11_φ4 : Fin 4 → ℝ := Fin.snoc half_15_11_φ3 (879907451/10000000000 : ℝ)

private theorem half_15_11_total4 : total half_15_11_φ4=(768129567/2000000000 : ℝ) := by
  change total (Fin.snoc half_15_11_φ3 (879907451/10000000000 : ℝ))=(768129567/2000000000 : ℝ)
  rw [alternate_total_snoc,half_15_11_total3]
  norm_num

private theorem half_15_11_bounds4 : ∀ l,0≤half_15_11_φ4 l ∧ half_15_11_φ4 l≤1 ∧
    0≤shiftExponents 9 half_15_11_φ4 l :=
  alternate_bounds_snoc half_15_11_φ3 (879907451/10000000000 : ℝ) half_15_11_bounds3 (by norm_num)

private def half_15_11_φ5 : Fin 5 → ℝ := Fin.snoc half_15_11_φ4 (38495951/500000000 : ℝ)

private theorem half_15_11_total5 : total half_15_11_φ5=(922113371/2000000000 : ℝ) := by
  change total (Fin.snoc half_15_11_φ4 (38495951/500000000 : ℝ))=(922113371/2000000000 : ℝ)
  rw [alternate_total_snoc,half_15_11_total4]
  norm_num

private theorem half_15_11_bounds5 : ∀ l,0≤half_15_11_φ5 l ∧ half_15_11_φ5 l≤1 ∧
    0≤shiftExponents 9 half_15_11_φ5 l :=
  alternate_bounds_snoc half_15_11_φ4 (38495951/500000000 : ℝ) half_15_11_bounds4 (by norm_num)

private def half_15_11_φ6 : Fin 6 → ℝ := Fin.snoc half_15_11_φ5 (274374497/5000000000 : ℝ)

private theorem half_15_11_total6 : total half_15_11_φ6=(5159315849/10000000000 : ℝ) := by
  change total (Fin.snoc half_15_11_φ5 (274374497/5000000000 : ℝ))=(5159315849/10000000000 : ℝ)
  rw [alternate_total_snoc,half_15_11_total5]
  norm_num

private theorem half_15_11_bounds6 : ∀ l,0≤half_15_11_φ6 l ∧ half_15_11_φ6 l≤1 ∧
    0≤shiftExponents 9 half_15_11_φ6 l :=
  alternate_bounds_snoc half_15_11_φ5 (274374497/5000000000 : ℝ) half_15_11_bounds5 (by norm_num)

private theorem half_15_11_prefix : PrefixCondition 9 half_15_11_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_15_11_φ1, half_15_11_φ2, half_15_11_φ3, half_15_11_φ4, half_15_11_φ5, half_15_11_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_15_11_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_15_11_φ6) (9522052453/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_15_11_φ6
    (fun i => (half_15_11_bounds6 i).1) (fun i => (half_15_11_bounds6 i).2.1)
    (fun i => (half_15_11_bounds6 i).2.2) half_15_11_prefix
  convert h using 1 <;> norm_num [half_15_11_total1, half_15_11_total2, half_15_11_total3, half_15_11_total4, half_15_11_total5, half_15_11_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_15_11_hx6 : SourcePowerBound
    (powerBoxCross 9 9 64 half_15_11_φ6) (38800774893/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 9) (r := 2) (v := 0) (w := 12) (D := 64)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_15_11_φ6 (by norm_num [half_15_11_total1, half_15_11_total2, half_15_11_total3, half_15_11_total4, half_15_11_total5, half_15_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_15_11_total1, half_15_11_total2, half_15_11_total3, half_15_11_total4, half_15_11_total5, half_15_11_total6, parameterExponent, curveLoss, dyadicExponent]) half_15_11_hF2
    (admissibleExponent_zero 9) (half_12_11)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_11_total1, half_15_11_total2, half_15_11_total3, half_15_11_total4, half_15_11_total5, half_15_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_11_hx5 : SourcePowerBound
    (powerBoxCross 9 10 32 half_15_11_φ5) (22213834881/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 10) (u := 8) (t := 11)
    (D := 32) (ψ := (274374497/5000000000 : ℝ)) half_15_11_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_11_bounds5 l).1) (fun l => (half_15_11_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_11_total1, half_15_11_total2, half_15_11_total3, half_15_11_total4, half_15_11_total5, half_15_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_11)
    (by simpa only [half_15_11_φ6, show (2:ℝ)*32=64 by norm_num] using half_15_11_hx6)
  exact h.weaken (by norm_num [half_15_11_total1, half_15_11_total2, half_15_11_total3, half_15_11_total4, half_15_11_total5, half_15_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_11_hx4 : SourcePowerBound
    (powerBoxCross 9 11 16 half_15_11_φ4) (53026083571/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (38495951/500000000 : ℝ)) half_15_11_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_11_bounds4 l).1) (fun l => (half_15_11_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_11_total1, half_15_11_total2, half_15_11_total3, half_15_11_total4, half_15_11_total5, half_15_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_11) (half_12_11)
    (by simpa only [half_15_11_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_11_hx5)
  exact h.weaken (by norm_num [half_15_11_total1, half_15_11_total2, half_15_11_total3, half_15_11_total4, half_15_11_total5, half_15_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_11_hx3 : SourcePowerBound
    (powerBoxCross 9 12 8 half_15_11_φ3) (64204806979/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (879907451/10000000000 : ℝ)) half_15_11_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_11_bounds3 l).1) (fun l => (half_15_11_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_11_total1, half_15_11_total2, half_15_11_total3, half_15_11_total4, half_15_11_total5, half_15_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_11) (half_13_11)
    (by simpa only [half_15_11_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_11_hx4)
  exact h.weaken (by norm_num [half_15_11_total1, half_15_11_total2, half_15_11_total3, half_15_11_total4, half_15_11_total5, half_15_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_11_hx2 : SourcePowerBound
    (powerBoxCross 9 13 4 half_15_11_φ2) (77912768537/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (950841759/10000000000 : ℝ)) half_15_11_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_11_bounds2 l).1) (fun l => (half_15_11_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_11_total1, half_15_11_total2, half_15_11_total3, half_15_11_total4, half_15_11_total5, half_15_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_11) (half_14_11)
    (by simpa only [half_15_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_11_hx3)
  exact h.weaken (by norm_num [half_15_11_total1, half_15_11_total2, half_15_11_total3, half_15_11_total4, half_15_11_total5, half_15_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_11_hx1 : SourcePowerBound
    (powerBoxCross 9 14 2 half_15_11_φ1) (37597434937/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (247596917/2500000000 : ℝ)) half_15_11_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_11_bounds1 l).1) (fun l => (half_15_11_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_11_total1, half_15_11_total2, half_15_11_total3, half_15_11_total4, half_15_11_total5, half_15_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_11) (half_15_10)
    (by simpa only [half_15_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_11_hx2)
  exact h.weaken (by norm_num [half_15_11_total1, half_15_11_total2, half_15_11_total3, half_15_11_total4, half_15_11_total5, half_15_11_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_15_11 : AdmissibleExponent 9 30 (53878492631/2500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 13) (ψ := (1019510957/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_14_11)
    (by simpa only [half_15_11_φ1] using half_15_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_11_total1, half_15_11_total2, half_15_11_total3, half_15_11_total4, half_15_11_total5, half_15_11_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_16_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1039049129/10000000000 : ℝ)

private theorem half_16_11_total1 : total half_16_11_φ1=(1039049129/10000000000 : ℝ) := by
  norm_num [half_16_11_φ1,total,emptyPhi,Fin.snoc]

private theorem half_16_11_bounds1 : ∀ l,0≤half_16_11_φ1 l ∧ half_16_11_φ1 l≤1 ∧
    0≤shiftExponents 9 half_16_11_φ1 l :=
  alternate_bounds_snoc emptyPhi (1039049129/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_16_11_φ2 : Fin 2 → ℝ := Fin.snoc half_16_11_φ1 (63368773/625000000 : ℝ)

private theorem half_16_11_total2 : total half_16_11_φ2=(2052949497/10000000000 : ℝ) := by
  change total (Fin.snoc half_16_11_φ1 (63368773/625000000 : ℝ))=(2052949497/10000000000 : ℝ)
  rw [alternate_total_snoc,half_16_11_total1]
  norm_num

private theorem half_16_11_bounds2 : ∀ l,0≤half_16_11_φ2 l ∧ half_16_11_φ2 l≤1 ∧
    0≤shiftExponents 9 half_16_11_φ2 l :=
  alternate_bounds_snoc half_16_11_φ1 (63368773/625000000 : ℝ) half_16_11_bounds1 (by norm_num)

private def half_16_11_φ3 : Fin 3 → ℝ := Fin.snoc half_16_11_φ2 (491441919/5000000000 : ℝ)

private theorem half_16_11_total3 : total half_16_11_φ3=(607166667/2000000000 : ℝ) := by
  change total (Fin.snoc half_16_11_φ2 (491441919/5000000000 : ℝ))=(607166667/2000000000 : ℝ)
  rw [alternate_total_snoc,half_16_11_total2]
  norm_num

private theorem half_16_11_bounds3 : ∀ l,0≤half_16_11_φ3 l ∧ half_16_11_φ3 l≤1 ∧
    0≤shiftExponents 9 half_16_11_φ3 l :=
  alternate_bounds_snoc half_16_11_φ2 (491441919/5000000000 : ℝ) half_16_11_bounds2 (by norm_num)

private def half_16_11_φ4 : Fin 4 → ℝ := Fin.snoc half_16_11_φ3 (850118/9765625 : ℝ)

private theorem half_16_11_total4 : total half_16_11_φ4=(3906354167/10000000000 : ℝ) := by
  change total (Fin.snoc half_16_11_φ3 (850118/9765625 : ℝ))=(3906354167/10000000000 : ℝ)
  rw [alternate_total_snoc,half_16_11_total3]
  norm_num

private theorem half_16_11_bounds4 : ∀ l,0≤half_16_11_φ4 l ∧ half_16_11_φ4 l≤1 ∧
    0≤shiftExponents 9 half_16_11_φ4 l :=
  alternate_bounds_snoc half_16_11_φ3 (850118/9765625 : ℝ) half_16_11_bounds3 (by norm_num)

private def half_16_11_φ5 : Fin 5 → ℝ := Fin.snoc half_16_11_φ4 (2975413/39062500 : ℝ)

private theorem half_16_11_total5 : total half_16_11_φ5=(933611979/2000000000 : ℝ) := by
  change total (Fin.snoc half_16_11_φ4 (2975413/39062500 : ℝ))=(933611979/2000000000 : ℝ)
  rw [alternate_total_snoc,half_16_11_total4]
  norm_num

private theorem half_16_11_bounds5 : ∀ l,0≤half_16_11_φ5 l ∧ half_16_11_φ5 l≤1 ∧
    0≤shiftExponents 9 half_16_11_φ5 l :=
  alternate_bounds_snoc half_16_11_φ4 (2975413/39062500 : ℝ) half_16_11_bounds4 (by norm_num)

private def half_16_11_φ6 : Fin 6 → ℝ := Fin.snoc half_16_11_φ5 (658359537/10000000000 : ℝ)

private theorem half_16_11_total6 : total half_16_11_φ6=(665802429/1250000000 : ℝ) := by
  change total (Fin.snoc half_16_11_φ5 (658359537/10000000000 : ℝ))=(665802429/1250000000 : ℝ)
  rw [alternate_total_snoc,half_16_11_total5]
  norm_num

private theorem half_16_11_bounds6 : ∀ l,0≤half_16_11_φ6 l ∧ half_16_11_φ6 l≤1 ∧
    0≤shiftExponents 9 half_16_11_φ6 l :=
  alternate_bounds_snoc half_16_11_φ5 (658359537/10000000000 : ℝ) half_16_11_bounds5 (by norm_num)

private theorem half_16_11_prefix : PrefixCondition 9 half_16_11_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_16_11_φ1, half_16_11_φ2, half_16_11_φ3, half_16_11_φ4, half_16_11_φ5, half_16_11_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_16_11_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_16_11_φ6) (1127592713/156250000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_16_11_φ6
    (fun i => (half_16_11_bounds6 i).1) (fun i => (half_16_11_bounds6 i).2.1)
    (fun i => (half_16_11_bounds6 i).2.2) half_16_11_prefix
  convert h using 1 <;> norm_num [half_16_11_total1, half_16_11_total2, half_16_11_total3, half_16_11_total4, half_16_11_total5, half_16_11_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_16_11_hx6 : SourcePowerBound
    (powerBoxCross 9 10 64 half_16_11_φ6) (41442473919/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 10) (r := 2) (v := 13) (w := 14) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_16_11_φ6 (by norm_num [half_16_11_total1, half_16_11_total2, half_16_11_total3, half_16_11_total4, half_16_11_total5, half_16_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_16_11_total1, half_16_11_total2, half_16_11_total3, half_16_11_total4, half_16_11_total5, half_16_11_total6, parameterExponent, curveLoss, dyadicExponent]) half_16_11_hF2
    (half_13_11) (half_14_11)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_11_total1, half_16_11_total2, half_16_11_total3, half_16_11_total4, half_16_11_total5, half_16_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_11_hx5 : SourcePowerBound
    (powerBoxCross 9 11 32 half_16_11_φ5) (12128092623/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 11) (u := 9) (t := 12)
    (D := 32) (ψ := (658359537/10000000000 : ℝ)) half_16_11_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_11_bounds5 l).1) (fun l => (half_16_11_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_11_total1, half_16_11_total2, half_16_11_total3, half_16_11_total4, half_16_11_total5, half_16_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_11) (half_12_11)
    (by simpa only [half_16_11_φ6, show (2:ℝ)*32=64 by norm_num] using half_16_11_hx6)
  exact h.weaken (by norm_num [half_16_11_total1, half_16_11_total2, half_16_11_total3, half_16_11_total4, half_16_11_total5, half_16_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_11_hx4 : SourcePowerBound
    (powerBoxCross 9 12 16 half_16_11_φ4) (115410952871/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (2975413/39062500 : ℝ)) half_16_11_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_11_bounds4 l).1) (fun l => (half_16_11_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_11_total1, half_16_11_total2, half_16_11_total3, half_16_11_total4, half_16_11_total5, half_16_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_11) (half_13_11)
    (by simpa only [half_16_11_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_11_hx5)
  exact h.weaken (by norm_num [half_16_11_total1, half_16_11_total2, half_16_11_total3, half_16_11_total4, half_16_11_total5, half_16_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_11_hx3 : SourcePowerBound
    (powerBoxCross 9 13 8 half_16_11_φ3) (34797587049/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (850118/9765625 : ℝ)) half_16_11_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_11_bounds3 l).1) (fun l => (half_16_11_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_11_total1, half_16_11_total2, half_16_11_total3, half_16_11_total4, half_16_11_total5, half_16_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_11) (half_14_11)
    (by simpa only [half_16_11_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_11_hx4)
  exact h.weaken (by norm_num [half_16_11_total1, half_16_11_total2, half_16_11_total3, half_16_11_total4, half_16_11_total5, half_16_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_11_hx2 : SourcePowerBound
    (powerBoxCross 9 14 4 half_16_11_φ2) (84652222239/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (491441919/5000000000 : ℝ)) half_16_11_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_11_bounds2 l).1) (fun l => (half_16_11_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_11_total1, half_16_11_total2, half_16_11_total3, half_16_11_total4, half_16_11_total5, half_16_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_11) (half_15_11)
    (by simpa only [half_16_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_11_hx3)
  exact h.weaken (by norm_num [half_16_11_total1, half_16_11_total2, half_16_11_total3, half_16_11_total4, half_16_11_total5, half_16_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_11_hx1 : SourcePowerBound
    (powerBoxCross 9 15 2 half_16_11_φ1) (204160059319/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (63368773/625000000 : ℝ)) half_16_11_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_11_bounds1 l).1) (fun l => (half_16_11_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_11_total1, half_16_11_total2, half_16_11_total3, half_16_11_total4, half_16_11_total5, half_16_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_11) (half_16_10)
    (by simpa only [half_16_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_11_hx2)
  exact h.weaken (by norm_num [half_16_11_total1, half_16_11_total2, half_16_11_total3, half_16_11_total4, half_16_11_total5, half_16_11_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_16_11 : AdmissibleExponent 9 32 (11714624203/500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 14) (ψ := (1039049129/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_15_11)
    (by simpa only [half_16_11_φ1] using half_16_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_11_total1, half_16_11_total2, half_16_11_total3, half_16_11_total4, half_16_11_total5, half_16_11_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_17_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (263873803/2500000000 : ℝ)

private theorem half_17_11_total1 : total half_17_11_φ1=(263873803/2500000000 : ℝ) := by
  norm_num [half_17_11_φ1,total,emptyPhi,Fin.snoc]

private theorem half_17_11_bounds1 : ∀ l,0≤half_17_11_φ1 l ∧ half_17_11_φ1 l≤1 ∧
    0≤shiftExponents 9 half_17_11_φ1 l :=
  alternate_bounds_snoc emptyPhi (263873803/2500000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_17_11_φ2 : Fin 2 → ℝ := Fin.snoc half_17_11_φ1 (8094521/78125000 : ℝ)

private theorem half_17_11_total2 : total half_17_11_φ2=(20915939/100000000 : ℝ) := by
  change total (Fin.snoc half_17_11_φ1 (8094521/78125000 : ℝ))=(20915939/100000000 : ℝ)
  rw [alternate_total_snoc,half_17_11_total1]
  norm_num

private theorem half_17_11_bounds2 : ∀ l,0≤half_17_11_φ2 l ∧ half_17_11_φ2 l≤1 ∧
    0≤shiftExponents 9 half_17_11_φ2 l :=
  alternate_bounds_snoc half_17_11_φ1 (8094521/78125000 : ℝ) half_17_11_bounds1 (by norm_num)

private def half_17_11_φ3 : Fin 3 → ℝ := Fin.snoc half_17_11_φ2 (494275381/5000000000 : ℝ)

private theorem half_17_11_total3 : total half_17_11_φ3=(1540072331/5000000000 : ℝ) := by
  change total (Fin.snoc half_17_11_φ2 (494275381/5000000000 : ℝ))=(1540072331/5000000000 : ℝ)
  rw [alternate_total_snoc,half_17_11_total2]
  norm_num

private theorem half_17_11_bounds3 : ∀ l,0≤half_17_11_φ3 l ∧ half_17_11_φ3 l≤1 ∧
    0≤shiftExponents 9 half_17_11_φ3 l :=
  alternate_bounds_snoc half_17_11_φ2 (494275381/5000000000 : ℝ) half_17_11_bounds2 (by norm_num)

private def half_17_11_φ4 : Fin 4 → ℝ := Fin.snoc half_17_11_φ3 (864981917/10000000000 : ℝ)

private theorem half_17_11_total4 : total half_17_11_φ4=(3945126579/10000000000 : ℝ) := by
  change total (Fin.snoc half_17_11_φ3 (864981917/10000000000 : ℝ))=(3945126579/10000000000 : ℝ)
  rw [alternate_total_snoc,half_17_11_total3]
  norm_num

private theorem half_17_11_bounds4 : ∀ l,0≤half_17_11_φ4 l ∧ half_17_11_φ4 l≤1 ∧
    0≤shiftExponents 9 half_17_11_φ4 l :=
  alternate_bounds_snoc half_17_11_φ3 (864981917/10000000000 : ℝ) half_17_11_bounds3 (by norm_num)

private def half_17_11_φ5 : Fin 5 → ℝ := Fin.snoc half_17_11_φ4 (756859177/10000000000 : ℝ)

private theorem half_17_11_total5 : total half_17_11_φ5=(1175496439/2500000000 : ℝ) := by
  change total (Fin.snoc half_17_11_φ4 (756859177/10000000000 : ℝ))=(1175496439/2500000000 : ℝ)
  rw [alternate_total_snoc,half_17_11_total4]
  norm_num

private theorem half_17_11_bounds5 : ∀ l,0≤half_17_11_φ5 l ∧ half_17_11_φ5 l≤1 ∧
    0≤shiftExponents 9 half_17_11_φ5 l :=
  alternate_bounds_snoc half_17_11_φ4 (756859177/10000000000 : ℝ) half_17_11_bounds4 (by norm_num)

private def half_17_11_φ6 : Fin 6 → ℝ := Fin.snoc half_17_11_φ5 (33112589/500000000 : ℝ)

private theorem half_17_11_total6 : total half_17_11_φ6=(167632423/312500000 : ℝ) := by
  change total (Fin.snoc half_17_11_φ5 (33112589/500000000 : ℝ))=(167632423/312500000 : ℝ)
  rw [alternate_total_snoc,half_17_11_total5]
  norm_num

private theorem half_17_11_bounds6 : ∀ l,0≤half_17_11_φ6 l ∧ half_17_11_φ6 l≤1 ∧
    0≤shiftExponents 9 half_17_11_φ6 l :=
  alternate_bounds_snoc half_17_11_φ5 (33112589/500000000 : ℝ) half_17_11_bounds5 (by norm_num)

private theorem half_17_11_prefix : PrefixCondition 9 half_17_11_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_17_11_φ1, half_17_11_φ2, half_17_11_φ3, half_17_11_φ4, half_17_11_φ5, half_17_11_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_17_11_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_17_11_φ6) (278352731/39062500 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_17_11_φ6
    (fun i => (half_17_11_bounds6 i).1) (fun i => (half_17_11_bounds6 i).2.1)
    (fun i => (half_17_11_bounds6 i).2.2) half_17_11_prefix
  convert h using 1 <;> norm_num [half_17_11_total1, half_17_11_total2, half_17_11_total3, half_17_11_total4, half_17_11_total5, half_17_11_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_17_11_hx6 : SourcePowerBound
    (powerBoxCross 9 11 64 half_17_11_φ6) (90605998137/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 11) (r := 2) (v := 14) (w := 15) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_17_11_φ6 (by norm_num [half_17_11_total1, half_17_11_total2, half_17_11_total3, half_17_11_total4, half_17_11_total5, half_17_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_17_11_total1, half_17_11_total2, half_17_11_total3, half_17_11_total4, half_17_11_total5, half_17_11_total6, parameterExponent, curveLoss, dyadicExponent]) half_17_11_hF2
    (half_14_11) (half_15_11)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_11_total1, half_17_11_total2, half_17_11_total3, half_17_11_total4, half_17_11_total5, half_17_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_11_hx5 : SourcePowerBound
    (powerBoxCross 9 12 32 half_17_11_φ5) (105855458117/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 12) (u := 10) (t := 13)
    (D := 32) (ψ := (33112589/500000000 : ℝ)) half_17_11_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_11_bounds5 l).1) (fun l => (half_17_11_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_11_total1, half_17_11_total2, half_17_11_total3, half_17_11_total4, half_17_11_total5, half_17_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_11) (half_13_11)
    (by simpa only [half_17_11_φ6, show (2:ℝ)*32=64 by norm_num] using half_17_11_hx6)
  exact h.weaken (by norm_num [half_17_11_total1, half_17_11_total2, half_17_11_total3, half_17_11_total4, half_17_11_total5, half_17_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_11_hx4 : SourcePowerBound
    (powerBoxCross 9 13 16 half_17_11_φ4) (62754573153/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (756859177/10000000000 : ℝ)) half_17_11_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_11_bounds4 l).1) (fun l => (half_17_11_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_11_total1, half_17_11_total2, half_17_11_total3, half_17_11_total4, half_17_11_total5, half_17_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_11) (half_14_11)
    (by simpa only [half_17_11_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_11_hx5)
  exact h.weaken (by norm_num [half_17_11_total1, half_17_11_total2, half_17_11_total3, half_17_11_total4, half_17_11_total5, half_17_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_11_hx3 : SourcePowerBound
    (powerBoxCross 9 14 8 half_17_11_φ3) (30162508687/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (864981917/10000000000 : ℝ)) half_17_11_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_11_bounds3 l).1) (fun l => (half_17_11_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_11_total1, half_17_11_total2, half_17_11_total3, half_17_11_total4, half_17_11_total5, half_17_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_11) (half_15_11)
    (by simpa only [half_17_11_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_11_hx4)
  exact h.weaken (by norm_num [half_17_11_total1, half_17_11_total2, half_17_11_total3, half_17_11_total4, half_17_11_total5, half_17_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_11_hx2 : SourcePowerBound
    (powerBoxCross 9 15 4 half_17_11_φ2) (183029336911/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (494275381/5000000000 : ℝ)) half_17_11_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_11_bounds2 l).1) (fun l => (half_17_11_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_11_total1, half_17_11_total2, half_17_11_total3, half_17_11_total4, half_17_11_total5, half_17_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_11) (half_16_11)
    (by simpa only [half_17_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_11_hx3)
  exact h.weaken (by norm_num [half_17_11_total1, half_17_11_total2, half_17_11_total3, half_17_11_total4, half_17_11_total5, half_17_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_11_hx1 : SourcePowerBound
    (powerBoxCross 9 16 2 half_17_11_φ1) (55154629941/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (8094521/78125000 : ℝ)) half_17_11_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_11_bounds1 l).1) (fun l => (half_17_11_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_11_total1, half_17_11_total2, half_17_11_total3, half_17_11_total4, half_17_11_total5, half_17_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_11) (half_17_10)
    (by simpa only [half_17_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_11_hx2)
  exact h.weaken (by norm_num [half_17_11_total1, half_17_11_total2, half_17_11_total3, half_17_11_total4, half_17_11_total5, half_17_11_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_17_11 : AdmissibleExponent 9 34 (31667358917/1250000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 15) (ψ := (263873803/2500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_16_11)
    (by simpa only [half_17_11_φ1] using half_17_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_11_total1, half_17_11_total2, half_17_11_total3, half_17_11_total4, half_17_11_total5, half_17_11_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_18_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1068394773/10000000000 : ℝ)

private theorem half_18_11_total1 : total half_18_11_φ1=(1068394773/10000000000 : ℝ) := by
  norm_num [half_18_11_φ1,total,emptyPhi,Fin.snoc]

private theorem half_18_11_bounds1 : ∀ l,0≤half_18_11_φ1 l ∧ half_18_11_φ1 l≤1 ∧
    0≤shiftExponents 9 half_18_11_φ1 l :=
  alternate_bounds_snoc emptyPhi (1068394773/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_18_11_φ2 : Fin 2 → ℝ := Fin.snoc half_18_11_φ1 (527051687/5000000000 : ℝ)

private theorem half_18_11_total2 : total half_18_11_φ2=(2122498147/10000000000 : ℝ) := by
  change total (Fin.snoc half_18_11_φ1 (527051687/5000000000 : ℝ))=(2122498147/10000000000 : ℝ)
  rw [alternate_total_snoc,half_18_11_total1]
  norm_num

private theorem half_18_11_bounds2 : ∀ l,0≤half_18_11_φ2 l ∧ half_18_11_φ2 l≤1 ∧
    0≤shiftExponents 9 half_18_11_φ2 l :=
  alternate_bounds_snoc half_18_11_φ1 (527051687/5000000000 : ℝ) half_18_11_bounds1 (by norm_num)

private def half_18_11_φ3 : Fin 3 → ℝ := Fin.snoc half_18_11_φ2 (984687731/10000000000 : ℝ)

private theorem half_18_11_total3 : total half_18_11_φ3=(1553592939/5000000000 : ℝ) := by
  change total (Fin.snoc half_18_11_φ2 (984687731/10000000000 : ℝ))=(1553592939/5000000000 : ℝ)
  rw [alternate_total_snoc,half_18_11_total2]
  norm_num

private theorem half_18_11_bounds3 : ∀ l,0≤half_18_11_φ3 l ∧ half_18_11_φ3 l≤1 ∧
    0≤shiftExponents 9 half_18_11_φ3 l :=
  alternate_bounds_snoc half_18_11_φ2 (984687731/10000000000 : ℝ) half_18_11_bounds2 (by norm_num)

private def half_18_11_φ4 : Fin 4 → ℝ := Fin.snoc half_18_11_φ3 (172320353/2000000000 : ℝ)

private theorem half_18_11_total4 : total half_18_11_φ4=(3968787643/10000000000 : ℝ) := by
  change total (Fin.snoc half_18_11_φ3 (172320353/2000000000 : ℝ))=(3968787643/10000000000 : ℝ)
  rw [alternate_total_snoc,half_18_11_total3]
  norm_num

private theorem half_18_11_bounds4 : ∀ l,0≤half_18_11_φ4 l ∧ half_18_11_φ4 l≤1 ∧
    0≤shiftExponents 9 half_18_11_φ4 l :=
  alternate_bounds_snoc half_18_11_φ3 (172320353/2000000000 : ℝ) half_18_11_bounds3 (by norm_num)

private def half_18_11_φ5 : Fin 5 → ℝ := Fin.snoc half_18_11_φ4 (94237693/1250000000 : ℝ)

private theorem half_18_11_total5 : total half_18_11_φ5=(4722689187/10000000000 : ℝ) := by
  change total (Fin.snoc half_18_11_φ4 (94237693/1250000000 : ℝ))=(4722689187/10000000000 : ℝ)
  rw [alternate_total_snoc,half_18_11_total4]
  norm_num

private theorem half_18_11_bounds5 : ∀ l,0≤half_18_11_φ5 l ∧ half_18_11_φ5 l≤1 ∧
    0≤shiftExponents 9 half_18_11_φ5 l :=
  alternate_bounds_snoc half_18_11_φ4 (94237693/1250000000 : ℝ) half_18_11_bounds4 (by norm_num)

private def half_18_11_φ6 : Fin 6 → ℝ := Fin.snoc half_18_11_φ5 (659663851/10000000000 : ℝ)

private theorem half_18_11_total6 : total half_18_11_φ6=(2691176519/5000000000 : ℝ) := by
  change total (Fin.snoc half_18_11_φ5 (659663851/10000000000 : ℝ))=(2691176519/5000000000 : ℝ)
  rw [alternate_total_snoc,half_18_11_total5]
  norm_num

private theorem half_18_11_bounds6 : ∀ l,0≤half_18_11_φ6 l ∧ half_18_11_φ6 l≤1 ∧
    0≤shiftExponents 9 half_18_11_φ6 l :=
  alternate_bounds_snoc half_18_11_φ5 (659663851/10000000000 : ℝ) half_18_11_bounds5 (by norm_num)

private theorem half_18_11_prefix : PrefixCondition 9 half_18_11_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_18_11_φ1, half_18_11_φ2, half_18_11_φ3, half_18_11_φ4, half_18_11_φ5, half_18_11_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_18_11_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_18_11_φ6) (4426470443/625000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_18_11_φ6
    (fun i => (half_18_11_bounds6 i).1) (fun i => (half_18_11_bounds6 i).2.1)
    (fun i => (half_18_11_bounds6 i).2.2) half_18_11_prefix
  convert h using 1 <;> norm_num [half_18_11_total1, half_18_11_total2, half_18_11_total3, half_18_11_total4, half_18_11_total5, half_18_11_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_18_11_hx6 : SourcePowerBound
    (powerBoxCross 9 12 64 half_18_11_φ6) (19769376013/2000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 12) (r := 2) (v := 0) (w := 16) (D := 64)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_18_11_φ6 (by norm_num [half_18_11_total1, half_18_11_total2, half_18_11_total3, half_18_11_total4, half_18_11_total5, half_18_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_18_11_total1, half_18_11_total2, half_18_11_total3, half_18_11_total4, half_18_11_total5, half_18_11_total6, parameterExponent, curveLoss, dyadicExponent]) half_18_11_hF2
    (admissibleExponent_zero 9) (half_16_11)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_18_11_total1, half_18_11_total2, half_18_11_total3, half_18_11_total4, half_18_11_total5, half_18_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_11_hx5 : SourcePowerBound
    (powerBoxCross 9 13 32 half_18_11_φ5) (115115616457/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 13) (u := 11) (t := 14)
    (D := 32) (ψ := (659663851/10000000000 : ℝ)) half_18_11_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_11_bounds5 l).1) (fun l => (half_18_11_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_11_total1, half_18_11_total2, half_18_11_total3, half_18_11_total4, half_18_11_total5, half_18_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_11) (half_14_11)
    (by simpa only [half_18_11_φ6, show (2:ℝ)*32=64 by norm_num] using half_18_11_hx6)
  exact h.weaken (by norm_num [half_18_11_total1, half_18_11_total2, half_18_11_total3, half_18_11_total4, half_18_11_total5, half_18_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_11_hx4 : SourcePowerBound
    (powerBoxCross 9 14 16 half_18_11_φ4) (17012119133/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 14) (u := 12) (t := 15)
    (D := 16) (ψ := (94237693/1250000000 : ℝ)) half_18_11_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_11_bounds4 l).1) (fun l => (half_18_11_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_11_total1, half_18_11_total2, half_18_11_total3, half_18_11_total4, half_18_11_total5, half_18_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_11) (half_15_11)
    (by simpa only [half_18_11_φ5, show (2:ℝ)*16=32 by norm_num] using half_18_11_hx5)
  exact h.weaken (by norm_num [half_18_11_total1, half_18_11_total2, half_18_11_total3, half_18_11_total4, half_18_11_total5, half_18_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_11_hx3 : SourcePowerBound
    (powerBoxCross 9 15 8 half_18_11_φ3) (40749520997/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 15) (u := 13) (t := 16)
    (D := 8) (ψ := (172320353/2000000000 : ℝ)) half_18_11_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_11_bounds3 l).1) (fun l => (half_18_11_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_11_total1, half_18_11_total2, half_18_11_total3, half_18_11_total4, half_18_11_total5, half_18_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_11) (half_16_11)
    (by simpa only [half_18_11_φ4, show (2:ℝ)*8=16 by norm_num] using half_18_11_hx4)
  exact h.weaken (by norm_num [half_18_11_total1, half_18_11_total2, half_18_11_total3, half_18_11_total4, half_18_11_total5, half_18_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_11_hx2 : SourcePowerBound
    (powerBoxCross 9 16 4 half_18_11_φ2) (7882835717/400000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 16) (u := 14) (t := 17)
    (D := 4) (ψ := (984687731/10000000000 : ℝ)) half_18_11_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_11_bounds2 l).1) (fun l => (half_18_11_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_11_total1, half_18_11_total2, half_18_11_total3, half_18_11_total4, half_18_11_total5, half_18_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_11) (half_17_11)
    (by simpa only [half_18_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_18_11_hx3)
  exact h.weaken (by norm_num [half_18_11_total1, half_18_11_total2, half_18_11_total3, half_18_11_total4, half_18_11_total5, half_18_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_11_hx1 : SourcePowerBound
    (powerBoxCross 9 17 2 half_18_11_φ1) (2966758419/125000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 17) (u := 15) (t := 18)
    (D := 2) (ψ := (527051687/5000000000 : ℝ)) half_18_11_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_11_bounds1 l).1) (fun l => (half_18_11_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_11_total1, half_18_11_total2, half_18_11_total3, half_18_11_total4, half_18_11_total5, half_18_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_11) (half_18_10)
    (by simpa only [half_18_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_18_11_hx2)
  exact h.weaken (by norm_num [half_18_11_total1, half_18_11_total2, half_18_11_total3, half_18_11_total4, half_18_11_total5, half_18_11_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_18_11 : AdmissibleExponent 9 36 (272597701029/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 16) (ψ := (1068394773/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_17_11)
    (by simpa only [half_18_11_φ1] using half_18_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_18_11_total1, half_18_11_total2, half_18_11_total3, half_18_11_total4, half_18_11_total5, half_18_11_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_19_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1078669909/10000000000 : ℝ)

private theorem half_19_11_total1 : total half_19_11_φ1=(1078669909/10000000000 : ℝ) := by
  norm_num [half_19_11_φ1,total,emptyPhi,Fin.snoc]

private theorem half_19_11_bounds1 : ∀ l,0≤half_19_11_φ1 l ∧ half_19_11_φ1 l≤1 ∧
    0≤shiftExponents 9 half_19_11_φ1 l :=
  alternate_bounds_snoc emptyPhi (1078669909/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_19_11_φ2 : Fin 2 → ℝ := Fin.snoc half_19_11_φ1 (267057807/2500000000 : ℝ)

private theorem half_19_11_total2 : total half_19_11_φ2=(2146901137/10000000000 : ℝ) := by
  change total (Fin.snoc half_19_11_φ1 (267057807/2500000000 : ℝ))=(2146901137/10000000000 : ℝ)
  rw [alternate_total_snoc,half_19_11_total1]
  norm_num

private theorem half_19_11_bounds2 : ∀ l,0≤half_19_11_φ2 l ∧ half_19_11_φ2 l≤1 ∧
    0≤shiftExponents 9 half_19_11_φ2 l :=
  alternate_bounds_snoc half_19_11_φ1 (267057807/2500000000 : ℝ) half_19_11_bounds1 (by norm_num)

private def half_19_11_φ3 : Fin 3 → ℝ := Fin.snoc half_19_11_φ2 (981637357/10000000000 : ℝ)

private theorem half_19_11_total3 : total half_19_11_φ3=(1564269247/5000000000 : ℝ) := by
  change total (Fin.snoc half_19_11_φ2 (981637357/10000000000 : ℝ))=(1564269247/5000000000 : ℝ)
  rw [alternate_total_snoc,half_19_11_total2]
  norm_num

private theorem half_19_11_bounds3 : ∀ l,0≤half_19_11_φ3 l ∧ half_19_11_φ3 l≤1 ∧
    0≤shiftExponents 9 half_19_11_φ3 l :=
  alternate_bounds_snoc half_19_11_φ2 (981637357/10000000000 : ℝ) half_19_11_bounds2 (by norm_num)

private def half_19_11_φ4 : Fin 4 → ℝ := Fin.snoc half_19_11_φ3 (53683293/625000000 : ℝ)

private theorem half_19_11_total4 : total half_19_11_φ4=(1993735591/5000000000 : ℝ) := by
  change total (Fin.snoc half_19_11_φ3 (53683293/625000000 : ℝ))=(1993735591/5000000000 : ℝ)
  rw [alternate_total_snoc,half_19_11_total3]
  norm_num

private theorem half_19_11_bounds4 : ∀ l,0≤half_19_11_φ4 l ∧ half_19_11_φ4 l≤1 ∧
    0≤shiftExponents 9 half_19_11_φ4 l :=
  alternate_bounds_snoc half_19_11_φ3 (53683293/625000000 : ℝ) half_19_11_bounds3 (by norm_num)

private def half_19_11_φ5 : Fin 5 → ℝ := Fin.snoc half_19_11_φ4 (375783051/5000000000 : ℝ)

private theorem half_19_11_total5 : total half_19_11_φ5=(1184759321/2500000000 : ℝ) := by
  change total (Fin.snoc half_19_11_φ4 (375783051/5000000000 : ℝ))=(1184759321/2500000000 : ℝ)
  rw [alternate_total_snoc,half_19_11_total4]
  norm_num

private theorem half_19_11_bounds5 : ∀ l,0≤half_19_11_φ5 l ∧ half_19_11_φ5 l≤1 ∧
    0≤shiftExponents 9 half_19_11_φ5 l :=
  alternate_bounds_snoc half_19_11_φ4 (375783051/5000000000 : ℝ) half_19_11_bounds4 (by norm_num)

private def half_19_11_φ6 : Fin 6 → ℝ := Fin.snoc half_19_11_φ5 (657620339/10000000000 : ℝ)

private theorem half_19_11_total6 : total half_19_11_φ6=(5396657623/10000000000 : ℝ) := by
  change total (Fin.snoc half_19_11_φ5 (657620339/10000000000 : ℝ))=(5396657623/10000000000 : ℝ)
  rw [alternate_total_snoc,half_19_11_total5]
  norm_num

private theorem half_19_11_bounds6 : ∀ l,0≤half_19_11_φ6 l ∧ half_19_11_φ6 l≤1 ∧
    0≤shiftExponents 9 half_19_11_φ6 l :=
  alternate_bounds_snoc half_19_11_φ5 (657620339/10000000000 : ℝ) half_19_11_bounds5 (by norm_num)

private theorem half_19_11_prefix : PrefixCondition 9 half_19_11_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_19_11_φ1, half_19_11_φ2, half_19_11_φ3, half_19_11_φ4, half_19_11_φ5, half_19_11_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_19_11_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_19_11_φ6) (8810027131/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_19_11_φ6
    (fun i => (half_19_11_bounds6 i).1) (fun i => (half_19_11_bounds6 i).2.1)
    (fun i => (half_19_11_bounds6 i).2.2) half_19_11_prefix
  convert h using 1 <;> norm_num [half_19_11_total1, half_19_11_total2, half_19_11_total3, half_19_11_total4, half_19_11_total5, half_19_11_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_19_11_hx6 : SourcePowerBound
    (powerBoxCross 9 13 64 half_19_11_φ6) (6706365381/625000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 13) (r := 2) (v := 17) (w := 18) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_19_11_φ6 (by norm_num [half_19_11_total1, half_19_11_total2, half_19_11_total3, half_19_11_total4, half_19_11_total5, half_19_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_19_11_total1, half_19_11_total2, half_19_11_total3, half_19_11_total4, half_19_11_total5, half_19_11_total6, parameterExponent, curveLoss, dyadicExponent]) half_19_11_hF2
    (half_17_11) (half_18_11)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_19_11_total1, half_19_11_total2, half_19_11_total3, half_19_11_total4, half_19_11_total5, half_19_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_11_hx5 : SourcePowerBound
    (powerBoxCross 9 14 32 half_19_11_φ5) (24921115267/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 14) (u := 12) (t := 15)
    (D := 32) (ψ := (657620339/10000000000 : ℝ)) half_19_11_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_11_bounds5 l).1) (fun l => (half_19_11_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_11_total1, half_19_11_total2, half_19_11_total3, half_19_11_total4, half_19_11_total5, half_19_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_11) (half_15_11)
    (by simpa only [half_19_11_φ6, show (2:ℝ)*32=64 by norm_num] using half_19_11_hx6)
  exact h.weaken (by norm_num [half_19_11_total1, half_19_11_total2, half_19_11_total3, half_19_11_total4, half_19_11_total5, half_19_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_11_hx4 : SourcePowerBound
    (powerBoxCross 9 15 16 half_19_11_φ4) (14693356143/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 15) (u := 13) (t := 16)
    (D := 16) (ψ := (375783051/5000000000 : ℝ)) half_19_11_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_11_bounds4 l).1) (fun l => (half_19_11_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_11_total1, half_19_11_total2, half_19_11_total3, half_19_11_total4, half_19_11_total5, half_19_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_11) (half_16_11)
    (by simpa only [half_19_11_φ5, show (2:ℝ)*16=32 by norm_num] using half_19_11_hx5)
  exact h.weaken (by norm_num [half_19_11_total1, half_19_11_total2, half_19_11_total3, half_19_11_total4, half_19_11_total5, half_19_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_11_hx3 : SourcePowerBound
    (powerBoxCross 9 16 8 half_19_11_φ3) (175447565833/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 16) (u := 14) (t := 17)
    (D := 8) (ψ := (53683293/625000000 : ℝ)) half_19_11_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_11_bounds3 l).1) (fun l => (half_19_11_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_11_total1, half_19_11_total2, half_19_11_total3, half_19_11_total4, half_19_11_total5, half_19_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_11) (half_17_11)
    (by simpa only [half_19_11_φ4, show (2:ℝ)*8=16 by norm_num] using half_19_11_hx4)
  exact h.weaken (by norm_num [half_19_11_total1, half_19_11_total2, half_19_11_total3, half_19_11_total4, half_19_11_total5, half_19_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_11_hx2 : SourcePowerBound
    (powerBoxCross 9 17 4 half_19_11_φ2) (211388392203/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 17) (u := 15) (t := 18)
    (D := 4) (ψ := (981637357/10000000000 : ℝ)) half_19_11_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_11_bounds2 l).1) (fun l => (half_19_11_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_11_total1, half_19_11_total2, half_19_11_total3, half_19_11_total4, half_19_11_total5, half_19_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_11) (half_18_11)
    (by simpa only [half_19_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_19_11_hx3)
  exact h.weaken (by norm_num [half_19_11_total1, half_19_11_total2, half_19_11_total3, half_19_11_total4, half_19_11_total5, half_19_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_11_hx1 : SourcePowerBound
    (powerBoxCross 9 18 2 half_19_11_φ1) (254272077211/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 18) (u := 16) (t := 19)
    (D := 2) (ψ := (267057807/2500000000 : ℝ)) half_19_11_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_11_bounds1 l).1) (fun l => (half_19_11_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_11_total1, half_19_11_total2, half_19_11_total3, half_19_11_total4, half_19_11_total5, half_19_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_11) (half_19_10)
    (by simpa only [half_19_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_19_11_hx2)
  exact h.weaken (by norm_num [half_19_11_total1, half_19_11_total2, half_19_11_total3, half_19_11_total4, half_19_11_total5, half_19_11_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_19_11 : AdmissibleExponent 9 38 (146012762013/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 17) (ψ := (1078669909/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_18_11)
    (by simpa only [half_19_11_φ1] using half_19_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_19_11_total1, half_19_11_total2, half_19_11_total3, half_19_11_total4, half_19_11_total5, half_19_11_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_20_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (43467129/400000000 : ℝ)

private theorem half_20_11_total1 : total half_20_11_φ1=(43467129/400000000 : ℝ) := by
  norm_num [half_20_11_φ1,total,emptyPhi,Fin.snoc]

private theorem half_20_11_bounds1 : ∀ l,0≤half_20_11_φ1 l ∧ half_20_11_φ1 l≤1 ∧
    0≤shiftExponents 9 half_20_11_φ1 l :=
  alternate_bounds_snoc emptyPhi (43467129/400000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_20_11_φ2 : Fin 2 → ℝ := Fin.snoc half_20_11_φ1 (6745909/62500000 : ℝ)

private theorem half_20_11_total2 : total half_20_11_φ2=(433204733/2000000000 : ℝ) := by
  change total (Fin.snoc half_20_11_φ1 (6745909/62500000 : ℝ))=(433204733/2000000000 : ℝ)
  rw [alternate_total_snoc,half_20_11_total1]
  norm_num

private theorem half_20_11_bounds2 : ∀ l,0≤half_20_11_φ2 l ∧ half_20_11_φ2 l≤1 ∧
    0≤shiftExponents 9 half_20_11_φ2 l :=
  alternate_bounds_snoc half_20_11_φ1 (6745909/62500000 : ℝ) half_20_11_bounds1 (by norm_num)

private def half_20_11_φ3 : Fin 3 → ℝ := Fin.snoc half_20_11_φ2 (979247041/10000000000 : ℝ)

private theorem half_20_11_total3 : total half_20_11_φ3=(1572635353/5000000000 : ℝ) := by
  change total (Fin.snoc half_20_11_φ2 (979247041/10000000000 : ℝ))=(1572635353/5000000000 : ℝ)
  rw [alternate_total_snoc,half_20_11_total2]
  norm_num

private theorem half_20_11_bounds3 : ∀ l,0≤half_20_11_φ3 l ∧ half_20_11_φ3 l≤1 ∧
    0≤shiftExponents 9 half_20_11_φ3 l :=
  alternate_bounds_snoc half_20_11_φ2 (979247041/10000000000 : ℝ) half_20_11_bounds2 (by norm_num)

private def half_20_11_φ4 : Fin 4 → ℝ := Fin.snoc half_20_11_φ3 (856841161/10000000000 : ℝ)

private theorem half_20_11_total4 : total half_20_11_φ4=(4002111867/10000000000 : ℝ) := by
  change total (Fin.snoc half_20_11_φ3 (856841161/10000000000 : ℝ))=(4002111867/10000000000 : ℝ)
  rw [alternate_total_snoc,half_20_11_total3]
  norm_num

private theorem half_20_11_bounds4 : ∀ l,0≤half_20_11_φ4 l ∧ half_20_11_φ4 l≤1 ∧
    0≤shiftExponents 9 half_20_11_φ4 l :=
  alternate_bounds_snoc half_20_11_φ3 (856841161/10000000000 : ℝ) half_20_11_bounds3 (by norm_num)

private def half_20_11_φ5 : Fin 5 → ℝ := Fin.snoc half_20_11_φ4 (46858501/625000000 : ℝ)

private theorem half_20_11_total5 : total half_20_11_φ5=(4751847883/10000000000 : ℝ) := by
  change total (Fin.snoc half_20_11_φ4 (46858501/625000000 : ℝ))=(4751847883/10000000000 : ℝ)
  rw [alternate_total_snoc,half_20_11_total4]
  norm_num

private theorem half_20_11_bounds5 : ∀ l,0≤half_20_11_φ5 l ∧ half_20_11_φ5 l≤1 ∧
    0≤shiftExponents 9 half_20_11_φ5 l :=
  alternate_bounds_snoc half_20_11_φ4 (46858501/625000000 : ℝ) half_20_11_bounds4 (by norm_num)

private def half_20_11_φ6 : Fin 6 → ℝ := Fin.snoc half_20_11_φ5 (328009507/5000000000 : ℝ)

private theorem half_20_11_total6 : total half_20_11_φ6=(5407866897/10000000000 : ℝ) := by
  change total (Fin.snoc half_20_11_φ5 (328009507/5000000000 : ℝ))=(5407866897/10000000000 : ℝ)
  rw [alternate_total_snoc,half_20_11_total5]
  norm_num

private theorem half_20_11_bounds6 : ∀ l,0≤half_20_11_φ6 l ∧ half_20_11_φ6 l≤1 ∧
    0≤shiftExponents 9 half_20_11_φ6 l :=
  alternate_bounds_snoc half_20_11_φ5 (328009507/5000000000 : ℝ) half_20_11_bounds5 (by norm_num)

private theorem half_20_11_prefix : PrefixCondition 9 half_20_11_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_20_11_φ1, half_20_11_φ2, half_20_11_φ3, half_20_11_φ4, half_20_11_φ5, half_20_11_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_20_11_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_20_11_φ6) (8776399309/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_20_11_φ6
    (fun i => (half_20_11_bounds6 i).1) (fun i => (half_20_11_bounds6 i).2.1)
    (fun i => (half_20_11_bounds6 i).2.2) half_20_11_prefix
  convert h using 1 <;> norm_num [half_20_11_total1, half_20_11_total2, half_20_11_total3, half_20_11_total4, half_20_11_total5, half_20_11_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_20_11_hx6 : SourcePowerBound
    (powerBoxCross 9 14 64 half_20_11_φ6) (14487365697/1250000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 14) (r := 2) (v := 18) (w := 19) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_20_11_φ6 (by norm_num [half_20_11_total1, half_20_11_total2, half_20_11_total3, half_20_11_total4, half_20_11_total5, half_20_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_20_11_total1, half_20_11_total2, half_20_11_total3, half_20_11_total4, half_20_11_total5, half_20_11_total6, parameterExponent, curveLoss, dyadicExponent]) half_20_11_hF2
    (half_18_11) (half_19_11)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_20_11_total1, half_20_11_total2, half_20_11_total3, half_20_11_total4, half_20_11_total5, half_20_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_11_hx5 : SourcePowerBound
    (powerBoxCross 9 15 32 half_20_11_φ5) (33569614439/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 15) (u := 13) (t := 16)
    (D := 32) (ψ := (328009507/5000000000 : ℝ)) half_20_11_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_11_bounds5 l).1) (fun l => (half_20_11_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_11_total1, half_20_11_total2, half_20_11_total3, half_20_11_total4, half_20_11_total5, half_20_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_11) (half_16_11)
    (by simpa only [half_20_11_φ6, show (2:ℝ)*32=64 by norm_num] using half_20_11_hx6)
  exact h.weaken (by norm_num [half_20_11_total1, half_20_11_total2, half_20_11_total3, half_20_11_total4, half_20_11_total5, half_20_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_11_hx4 : SourcePowerBound
    (powerBoxCross 9 16 16 half_20_11_φ4) (157976864143/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 16) (u := 14) (t := 17)
    (D := 16) (ψ := (46858501/625000000 : ℝ)) half_20_11_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_11_bounds4 l).1) (fun l => (half_20_11_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_11_total1, half_20_11_total2, half_20_11_total3, half_20_11_total4, half_20_11_total5, half_20_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_11) (half_17_11)
    (by simpa only [half_20_11_φ5, show (2:ℝ)*16=32 by norm_num] using half_20_11_hx5)
  exact h.weaken (by norm_num [half_20_11_total1, half_20_11_total2, half_20_11_total3, half_20_11_total4, half_20_11_total5, half_20_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_11_hx3 : SourcePowerBound
    (powerBoxCross 9 17 8 half_20_11_φ3) (9405877979/500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 17) (u := 15) (t := 18)
    (D := 8) (ψ := (856841161/10000000000 : ℝ)) half_20_11_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_11_bounds3 l).1) (fun l => (half_20_11_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_11_total1, half_20_11_total2, half_20_11_total3, half_20_11_total4, half_20_11_total5, half_20_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_11) (half_18_11)
    (by simpa only [half_20_11_φ4, show (2:ℝ)*8=16 by norm_num] using half_20_11_hx4)
  exact h.weaken (by norm_num [half_20_11_total1, half_20_11_total2, half_20_11_total3, half_20_11_total4, half_20_11_total5, half_20_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_11_hx2 : SourcePowerBound
    (powerBoxCross 9 18 4 half_20_11_φ2) (225938313529/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 18) (u := 16) (t := 19)
    (D := 4) (ψ := (979247041/10000000000 : ℝ)) half_20_11_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_11_bounds2 l).1) (fun l => (half_20_11_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_11_total1, half_20_11_total2, half_20_11_total3, half_20_11_total4, half_20_11_total5, half_20_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_11) (half_19_11)
    (by simpa only [half_20_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_20_11_hx3)
  exact h.weaken (by norm_num [half_20_11_total1, half_20_11_total2, half_20_11_total3, half_20_11_total4, half_20_11_total5, half_20_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_11_hx1 : SourcePowerBound
    (powerBoxCross 9 19 2 half_20_11_φ1) (54275684889/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 19) (u := 17) (t := 20)
    (D := 2) (ψ := (6745909/62500000 : ℝ)) half_20_11_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_11_bounds1 l).1) (fun l => (half_20_11_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_11_total1, half_20_11_total2, half_20_11_total3, half_20_11_total4, half_20_11_total5, half_20_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_11) (half_20_10)
    (by simpa only [half_20_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_20_11_hx2)
  exact h.weaken (by norm_num [half_20_11_total1, half_20_11_total2, half_20_11_total3, half_20_11_total4, half_20_11_total5, half_20_11_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_20_11 : AdmissibleExponent 9 40 (31158551877/1000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 18) (ψ := (43467129/400000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_19_11)
    (by simpa only [half_20_11_φ1] using half_20_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_20_11_total1, half_20_11_total2, half_20_11_total3, half_20_11_total4, half_20_11_total5, half_20_11_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_21_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (546465569/5000000000 : ℝ)

private theorem half_21_11_total1 : total half_21_11_φ1=(546465569/5000000000 : ℝ) := by
  norm_num [half_21_11_φ1,total,emptyPhi,Fin.snoc]

private theorem half_21_11_bounds1 : ∀ l,0≤half_21_11_φ1 l ∧ half_21_11_φ1 l≤1 ∧
    0≤shiftExponents 9 half_21_11_φ1 l :=
  alternate_bounds_snoc emptyPhi (546465569/5000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_21_11_φ2 : Fin 2 → ℝ := Fin.snoc half_21_11_φ1 (1087991173/10000000000 : ℝ)

private theorem half_21_11_total2 : total half_21_11_φ2=(2180922311/10000000000 : ℝ) := by
  change total (Fin.snoc half_21_11_φ1 (1087991173/10000000000 : ℝ))=(2180922311/10000000000 : ℝ)
  rw [alternate_total_snoc,half_21_11_total1]
  norm_num

private theorem half_21_11_bounds2 : ∀ l,0≤half_21_11_φ2 l ∧ half_21_11_φ2 l≤1 ∧
    0≤shiftExponents 9 half_21_11_φ2 l :=
  alternate_bounds_snoc half_21_11_φ1 (1087991173/10000000000 : ℝ) half_21_11_bounds1 (by norm_num)

private def half_21_11_φ3 : Fin 3 → ℝ := Fin.snoc half_21_11_φ2 (97738471/1000000000 : ℝ)

private theorem half_21_11_total3 : total half_21_11_φ3=(3158307021/10000000000 : ℝ) := by
  change total (Fin.snoc half_21_11_φ2 (97738471/1000000000 : ℝ))=(3158307021/10000000000 : ℝ)
  rw [alternate_total_snoc,half_21_11_total2]
  norm_num

private theorem half_21_11_bounds3 : ∀ l,0≤half_21_11_φ3 l ∧ half_21_11_φ3 l≤1 ∧
    0≤shiftExponents 9 half_21_11_φ3 l :=
  alternate_bounds_snoc half_21_11_φ2 (97738471/1000000000 : ℝ) half_21_11_bounds2 (by norm_num)

private def half_21_11_φ4 : Fin 4 → ℝ := Fin.snoc half_21_11_φ3 (427605811/5000000000 : ℝ)

private theorem half_21_11_total4 : total half_21_11_φ4=(4013518643/10000000000 : ℝ) := by
  change total (Fin.snoc half_21_11_φ3 (427605811/5000000000 : ℝ))=(4013518643/10000000000 : ℝ)
  rw [alternate_total_snoc,half_21_11_total3]
  norm_num

private theorem half_21_11_bounds4 : ∀ l,0≤half_21_11_φ4 l ∧ half_21_11_φ4 l≤1 ∧
    0≤shiftExponents 9 half_21_11_φ4 l :=
  alternate_bounds_snoc half_21_11_φ3 (427605811/5000000000 : ℝ) half_21_11_bounds3 (by norm_num)

private def half_21_11_φ5 : Fin 5 → ℝ := Fin.snoc half_21_11_φ4 (748310169/10000000000 : ℝ)

private theorem half_21_11_total5 : total half_21_11_φ5=(1190457203/2500000000 : ℝ) := by
  change total (Fin.snoc half_21_11_φ4 (748310169/10000000000 : ℝ))=(1190457203/2500000000 : ℝ)
  rw [alternate_total_snoc,half_21_11_total4]
  norm_num

private theorem half_21_11_bounds5 : ∀ l,0≤half_21_11_φ5 l ∧ half_21_11_φ5 l≤1 ∧
    0≤shiftExponents 9 half_21_11_φ5 l :=
  alternate_bounds_snoc half_21_11_φ4 (748310169/10000000000 : ℝ) half_21_11_bounds4 (by norm_num)

private def half_21_11_φ6 : Fin 6 → ℝ := Fin.snoc half_21_11_φ5 (327385699/5000000000 : ℝ)

private theorem half_21_11_total6 : total half_21_11_φ6=(541660021/1000000000 : ℝ) := by
  change total (Fin.snoc half_21_11_φ5 (327385699/5000000000 : ℝ))=(541660021/1000000000 : ℝ)
  rw [alternate_total_snoc,half_21_11_total5]
  norm_num

private theorem half_21_11_bounds6 : ∀ l,0≤half_21_11_φ6 l ∧ half_21_11_φ6 l≤1 ∧
    0≤shiftExponents 9 half_21_11_φ6 l :=
  alternate_bounds_snoc half_21_11_φ5 (327385699/5000000000 : ℝ) half_21_11_bounds5 (by norm_num)

private theorem half_21_11_prefix : PrefixCondition 9 half_21_11_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_21_11_φ1, half_21_11_φ2, half_21_11_φ3, half_21_11_φ4, half_21_11_φ5, half_21_11_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_21_11_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_21_11_φ6) (875019937/125000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_21_11_φ6
    (fun i => (half_21_11_bounds6 i).1) (fun i => (half_21_11_bounds6 i).2.1)
    (fun i => (half_21_11_bounds6 i).2.2) half_21_11_prefix
  convert h using 1 <;> norm_num [half_21_11_total1, half_21_11_total2, half_21_11_total3, half_21_11_total4, half_21_11_total5, half_21_11_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_21_11_hx6 : SourcePowerBound
    (powerBoxCross 9 15 64 half_21_11_φ6) (62304736919/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 15) (r := 2) (v := 0) (w := 20) (D := 64)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_21_11_φ6 (by norm_num [half_21_11_total1, half_21_11_total2, half_21_11_total3, half_21_11_total4, half_21_11_total5, half_21_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_21_11_total1, half_21_11_total2, half_21_11_total3, half_21_11_total4, half_21_11_total5, half_21_11_total6, parameterExponent, curveLoss, dyadicExponent]) half_21_11_hF2
    (admissibleExponent_zero 9) (half_20_11)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_21_11_total1, half_21_11_total2, half_21_11_total3, half_21_11_total4, half_21_11_total5, half_21_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_11_hx5 : SourcePowerBound
    (powerBoxCross 9 16 32 half_21_11_φ5) (72051612887/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 16) (u := 14) (t := 17)
    (D := 32) (ψ := (327385699/5000000000 : ℝ)) half_21_11_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_11_bounds5 l).1) (fun l => (half_21_11_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_11_total1, half_21_11_total2, half_21_11_total3, half_21_11_total4, half_21_11_total5, half_21_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_11) (half_17_11)
    (by simpa only [half_21_11_φ6, show (2:ℝ)*32=64 by norm_num] using half_21_11_hx6)
  exact h.weaken (by norm_num [half_21_11_total1, half_21_11_total2, half_21_11_total3, half_21_11_total4, half_21_11_total5, half_21_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_11_hx4 : SourcePowerBound
    (powerBoxCross 9 17 16 half_21_11_φ4) (84595699347/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 17) (u := 15) (t := 18)
    (D := 16) (ψ := (748310169/10000000000 : ℝ)) half_21_11_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_11_bounds4 l).1) (fun l => (half_21_11_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_11_total1, half_21_11_total2, half_21_11_total3, half_21_11_total4, half_21_11_total5, half_21_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_11) (half_18_11)
    (by simpa only [half_21_11_φ5, show (2:ℝ)*16=32 by norm_num] using half_21_11_hx5)
  exact h.weaken (by norm_num [half_21_11_total1, half_21_11_total2, half_21_11_total3, half_21_11_total4, half_21_11_total5, half_21_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_11_hx3 : SourcePowerBound
    (powerBoxCross 9 18 8 half_21_11_φ3) (200970911897/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 18) (u := 16) (t := 19)
    (D := 8) (ψ := (427605811/5000000000 : ℝ)) half_21_11_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_11_bounds3 l).1) (fun l => (half_21_11_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_11_total1, half_21_11_total2, half_21_11_total3, half_21_11_total4, half_21_11_total5, half_21_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_11) (half_19_11)
    (by simpa only [half_21_11_φ4, show (2:ℝ)*8=16 by norm_num] using half_21_11_hx4)
  exact h.weaken (by norm_num [half_21_11_total1, half_21_11_total2, half_21_11_total3, half_21_11_total4, half_21_11_total5, half_21_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_11_hx2 : SourcePowerBound
    (powerBoxCross 9 19 4 half_21_11_φ2) (240681568031/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 19) (u := 17) (t := 20)
    (D := 4) (ψ := (97738471/1000000000 : ℝ)) half_21_11_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_11_bounds2 l).1) (fun l => (half_21_11_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_11_total1, half_21_11_total2, half_21_11_total3, half_21_11_total4, half_21_11_total5, half_21_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_11) (half_20_11)
    (by simpa only [half_21_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_21_11_hx3)
  exact h.weaken (by norm_num [half_21_11_total1, half_21_11_total2, half_21_11_total3, half_21_11_total4, half_21_11_total5, half_21_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_11_hx1 : SourcePowerBound
    (powerBoxCross 9 20 2 half_21_11_φ1) (72156074589/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 20) (u := 18) (t := 21)
    (D := 2) (ψ := (1087991173/10000000000 : ℝ)) half_21_11_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_11_bounds1 l).1) (fun l => (half_21_11_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_11_total1, half_21_11_total2, half_21_11_total3, half_21_11_total4, half_21_11_total5, half_21_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_19_11) (half_21_10)
    (by simpa only [half_21_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_21_11_hx2)
  exact h.weaken (by norm_num [half_21_11_total1, half_21_11_total2, half_21_11_total3, half_21_11_total4, half_21_11_total5, half_21_11_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_21_11 : AdmissibleExponent 9 42 (165624306369/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 19) (ψ := (546465569/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_20_11)
    (by simpa only [half_21_11_φ1] using half_21_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_21_11_total1, half_21_11_total2, half_21_11_total3, half_21_11_total4, half_21_11_total5, half_21_11_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_22_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1097870437/10000000000 : ℝ)

private theorem half_22_11_total1 : total half_22_11_φ1=(1097870437/10000000000 : ℝ) := by
  norm_num [half_22_11_φ1,total,emptyPhi,Fin.snoc]

private theorem half_22_11_bounds1 : ∀ l,0≤half_22_11_φ1 l ∧ half_22_11_φ1 l≤1 ∧
    0≤shiftExponents 9 half_22_11_φ1 l :=
  alternate_bounds_snoc emptyPhi (1097870437/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_22_11_φ2 : Fin 2 → ℝ := Fin.snoc half_22_11_φ1 (136849149/1250000000 : ℝ)

private theorem half_22_11_total2 : total half_22_11_φ2=(2192663629/10000000000 : ℝ) := by
  change total (Fin.snoc half_22_11_φ1 (136849149/1250000000 : ℝ))=(2192663629/10000000000 : ℝ)
  rw [alternate_total_snoc,half_22_11_total1]
  norm_num

private theorem half_22_11_bounds2 : ∀ l,0≤half_22_11_φ2 l ∧ half_22_11_φ2 l≤1 ∧
    0≤shiftExponents 9 half_22_11_φ2 l :=
  alternate_bounds_snoc half_22_11_φ1 (136849149/1250000000 : ℝ) half_22_11_bounds1 (by norm_num)

private def half_22_11_φ3 : Fin 3 → ℝ := Fin.snoc half_22_11_φ2 (487958523/5000000000 : ℝ)

private theorem half_22_11_total3 : total half_22_11_φ3=(126743227/400000000 : ℝ) := by
  change total (Fin.snoc half_22_11_φ2 (487958523/5000000000 : ℝ))=(126743227/400000000 : ℝ)
  rw [alternate_total_snoc,half_22_11_total2]
  norm_num

private theorem half_22_11_bounds3 : ∀ l,0≤half_22_11_φ3 l ∧ half_22_11_φ3 l≤1 ∧
    0≤shiftExponents 9 half_22_11_φ3 l :=
  alternate_bounds_snoc half_22_11_φ2 (487958523/5000000000 : ℝ) half_22_11_bounds2 (by norm_num)

private def half_22_11_φ4 : Fin 4 → ℝ := Fin.snoc half_22_11_φ3 (170785483/2000000000 : ℝ)

private theorem half_22_11_total4 : total half_22_11_φ4=(402250809/1000000000 : ℝ) := by
  change total (Fin.snoc half_22_11_φ3 (170785483/2000000000 : ℝ))=(402250809/1000000000 : ℝ)
  rw [alternate_total_snoc,half_22_11_total3]
  norm_num

private theorem half_22_11_bounds4 : ∀ l,0≤half_22_11_φ4 l ∧ half_22_11_φ4 l≤1 ∧
    0≤shiftExponents 9 half_22_11_φ4 l :=
  alternate_bounds_snoc half_22_11_φ3 (170785483/2000000000 : ℝ) half_22_11_bounds3 (by norm_num)

private def half_22_11_φ5 : Fin 5 → ℝ := Fin.snoc half_22_11_φ4 (93398311/1250000000 : ℝ)

private theorem half_22_11_total5 : total half_22_11_φ5=(2384847289/5000000000 : ℝ) := by
  change total (Fin.snoc half_22_11_φ4 (93398311/1250000000 : ℝ))=(2384847289/5000000000 : ℝ)
  rw [alternate_total_snoc,half_22_11_total4]
  norm_num

private theorem half_22_11_bounds5 : ∀ l,0≤half_22_11_φ5 l ∧ half_22_11_φ5 l≤1 ∧
    0≤shiftExponents 9 half_22_11_φ5 l :=
  alternate_bounds_snoc half_22_11_φ4 (93398311/1250000000 : ℝ) half_22_11_bounds4 (by norm_num)

private def half_22_11_φ6 : Fin 6 → ℝ := Fin.snoc half_22_11_φ5 (653788177/10000000000 : ℝ)

private theorem half_22_11_total6 : total half_22_11_φ6=(1084696551/2000000000 : ℝ) := by
  change total (Fin.snoc half_22_11_φ5 (653788177/10000000000 : ℝ))=(1084696551/2000000000 : ℝ)
  rw [alternate_total_snoc,half_22_11_total5]
  norm_num

private theorem half_22_11_bounds6 : ∀ l,0≤half_22_11_φ6 l ∧ half_22_11_φ6 l≤1 ∧
    0≤shiftExponents 9 half_22_11_φ6 l :=
  alternate_bounds_snoc half_22_11_φ5 (653788177/10000000000 : ℝ) half_22_11_bounds5 (by norm_num)

private theorem half_22_11_prefix : PrefixCondition 9 half_22_11_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_22_11_φ1, half_22_11_φ2, half_22_11_φ3, half_22_11_φ4, half_22_11_φ5, half_22_11_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_22_11_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_22_11_φ6) (1745910347/250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_22_11_φ6
    (fun i => (half_22_11_bounds6 i).1) (fun i => (half_22_11_bounds6 i).2.1)
    (fun i => (half_22_11_bounds6 i).2.2) half_22_11_prefix
  convert h using 1 <;> norm_num [half_22_11_total1, half_22_11_total2, half_22_11_total3, half_22_11_total4, half_22_11_total5, half_22_11_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_22_11_hx6 : SourcePowerBound
    (powerBoxCross 9 16 64 half_22_11_φ6) (66708371473/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 16) (r := 2) (v := 21) (w := 22) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_22_11_φ6 (by norm_num [half_22_11_total1, half_22_11_total2, half_22_11_total3, half_22_11_total4, half_22_11_total5, half_22_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_22_11_total1, half_22_11_total2, half_22_11_total3, half_22_11_total4, half_22_11_total5, half_22_11_total6, parameterExponent, curveLoss, dyadicExponent]) half_22_11_hF2
    (half_21_11) (half_22_10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_22_11_total1, half_22_11_total2, half_22_11_total3, half_22_11_total4, half_22_11_total5, half_22_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_11_hx5 : SourcePowerBound
    (powerBoxCross 9 17 32 half_22_11_φ5) (154051771591/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 17) (u := 15) (t := 18)
    (D := 32) (ψ := (653788177/10000000000 : ℝ)) half_22_11_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_11_bounds5 l).1) (fun l => (half_22_11_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_11_total1, half_22_11_total2, half_22_11_total3, half_22_11_total4, half_22_11_total5, half_22_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_11) (half_18_11)
    (by simpa only [half_22_11_φ6, show (2:ℝ)*32=64 by norm_num] using half_22_11_hx6)
  exact h.weaken (by norm_num [half_22_11_total1, half_22_11_total2, half_22_11_total3, half_22_11_total4, half_22_11_total5, half_22_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_11_hx4 : SourcePowerBound
    (powerBoxCross 9 18 16 half_22_11_φ4) (180543440857/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 18) (u := 16) (t := 19)
    (D := 16) (ψ := (93398311/1250000000 : ℝ)) half_22_11_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_11_bounds4 l).1) (fun l => (half_22_11_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_11_total1, half_22_11_total2, half_22_11_total3, half_22_11_total4, half_22_11_total5, half_22_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_11) (half_19_11)
    (by simpa only [half_22_11_φ5, show (2:ℝ)*16=32 by norm_num] using half_22_11_hx5)
  exact h.weaken (by norm_num [half_22_11_total1, half_22_11_total2, half_22_11_total3, half_22_11_total4, half_22_11_total5, half_22_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_11_hx3 : SourcePowerBound
    (powerBoxCross 9 19 8 half_22_11_φ3) (213969694207/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 19) (u := 17) (t := 20)
    (D := 8) (ψ := (170785483/2000000000 : ℝ)) half_22_11_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_11_bounds3 l).1) (fun l => (half_22_11_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_11_total1, half_22_11_total2, half_22_11_total3, half_22_11_total4, half_22_11_total5, half_22_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_11) (half_20_11)
    (by simpa only [half_22_11_φ4, show (2:ℝ)*8=16 by norm_num] using half_22_11_hx4)
  exact h.weaken (by norm_num [half_22_11_total1, half_22_11_total2, half_22_11_total3, half_22_11_total4, half_22_11_total5, half_22_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_11_hx2 : SourcePowerBound
    (powerBoxCross 9 20 4 half_22_11_φ2) (255577125043/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 20) (u := 18) (t := 21)
    (D := 4) (ψ := (487958523/5000000000 : ℝ)) half_22_11_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_11_bounds2 l).1) (fun l => (half_22_11_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_11_total1, half_22_11_total2, half_22_11_total3, half_22_11_total4, half_22_11_total5, half_22_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_19_11) (half_21_11)
    (by simpa only [half_22_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_22_11_hx3)
  exact h.weaken (by norm_num [half_22_11_total1, half_22_11_total2, half_22_11_total3, half_22_11_total4, half_22_11_total5, half_22_11_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_11_hx1 : SourcePowerBound
    (powerBoxCross 9 21 2 half_22_11_φ1) (15298983863/500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 21) (u := 19) (t := 22)
    (D := 2) (ψ := (136849149/1250000000 : ℝ)) half_22_11_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_11_bounds1 l).1) (fun l => (half_22_11_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_11_total1, half_22_11_total2, half_22_11_total3, half_22_11_total4, half_22_11_total5, half_22_11_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_20_11) (half_22_10)
    (by simpa only [half_22_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_22_11_hx2)
  exact h.weaken (by norm_num [half_22_11_total1, half_22_11_total2, half_22_11_total3, half_22_11_total4, half_22_11_total5, half_22_11_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_22_11 : AdmissibleExponent 9 44 (350992365177/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 20) (ψ := (1097870437/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_21_11)
    (by simpa only [half_22_11_φ1] using half_22_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_22_11_total1, half_22_11_total2, half_22_11_total3, half_22_11_total4, half_22_11_total5, half_22_11_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_10_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (220138941/2500000000 : ℝ)

private theorem half_10_12_total1 : total half_10_12_φ1=(220138941/2500000000 : ℝ) := by
  norm_num [half_10_12_φ1,total,emptyPhi,Fin.snoc]

private theorem half_10_12_bounds1 : ∀ l,0≤half_10_12_φ1 l ∧ half_10_12_φ1 l≤1 ∧
    0≤shiftExponents 9 half_10_12_φ1 l :=
  alternate_bounds_snoc emptyPhi (220138941/2500000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_10_12_φ2 : Fin 2 → ℝ := Fin.snoc half_10_12_φ1 (821568477/10000000000 : ℝ)

private theorem half_10_12_total2 : total half_10_12_φ2=(1702124241/10000000000 : ℝ) := by
  change total (Fin.snoc half_10_12_φ1 (821568477/10000000000 : ℝ))=(1702124241/10000000000 : ℝ)
  rw [alternate_total_snoc,half_10_12_total1]
  norm_num

private theorem half_10_12_bounds2 : ∀ l,0≤half_10_12_φ2 l ∧ half_10_12_φ2 l≤1 ∧
    0≤shiftExponents 9 half_10_12_φ2 l :=
  alternate_bounds_snoc half_10_12_φ1 (821568477/10000000000 : ℝ) half_10_12_bounds1 (by norm_num)

private def half_10_12_φ3 : Fin 3 → ℝ := Fin.snoc half_10_12_φ2 (143409611/2000000000 : ℝ)

private theorem half_10_12_total3 : total half_10_12_φ3=(302396537/1250000000 : ℝ) := by
  change total (Fin.snoc half_10_12_φ2 (143409611/2000000000 : ℝ))=(302396537/1250000000 : ℝ)
  rw [alternate_total_snoc,half_10_12_total2]
  norm_num

private theorem half_10_12_bounds3 : ∀ l,0≤half_10_12_φ3 l ∧ half_10_12_φ3 l≤1 ∧
    0≤shiftExponents 9 half_10_12_φ3 l :=
  alternate_bounds_snoc half_10_12_φ2 (143409611/2000000000 : ℝ) half_10_12_bounds2 (by norm_num)

private def half_10_12_φ4 : Fin 4 → ℝ := Fin.snoc half_10_12_φ3 (225106501/5000000000 : ℝ)

private theorem half_10_12_total4 : total half_10_12_φ4=(1434692649/5000000000 : ℝ) := by
  change total (Fin.snoc half_10_12_φ3 (225106501/5000000000 : ℝ))=(1434692649/5000000000 : ℝ)
  rw [alternate_total_snoc,half_10_12_total3]
  norm_num

private theorem half_10_12_bounds4 : ∀ l,0≤half_10_12_φ4 l ∧ half_10_12_φ4 l≤1 ∧
    0≤shiftExponents 9 half_10_12_φ4 l :=
  alternate_bounds_snoc half_10_12_φ3 (225106501/5000000000 : ℝ) half_10_12_bounds3 (by norm_num)

private theorem half_10_12_prefix : PrefixCondition 9 half_10_12_φ4 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, half_10_12_φ4, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_10_12_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 16 half_10_12_φ4) (4445922053/625000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 9) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_12_φ4
    (fun i => (half_10_12_bounds4 i).1) (fun i => (half_10_12_bounds4 i).2.1)
    (fun i => (half_10_12_bounds4 i).2.2) half_10_12_prefix
  convert h using 1 <;> norm_num [half_10_12_total1, half_10_12_total2, half_10_12_total3, half_10_12_total4, parameterExponent, curveLoss, dyadicExponent]

private theorem half_10_12_hx4 : SourcePowerBound
    (powerBoxCross 9 6 16 half_10_12_φ4) (69145115513/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 6) (r := 2) (v := 0) (w := 8) (D := 16)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_10_12_φ4 (by norm_num [half_10_12_total1, half_10_12_total2, half_10_12_total3, half_10_12_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_10_12_total1, half_10_12_total2, half_10_12_total3, half_10_12_total4, parameterExponent, curveLoss, dyadicExponent]) half_10_12_hF2
    (admissibleExponent_zero 9) (SeedCompletionHigher9SimpleSeeds.degree9_half_8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_12_total1, half_10_12_total2, half_10_12_total3, half_10_12_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_10_12_hx3 : SourcePowerBound
    (powerBoxCross 9 7 8 half_10_12_φ3) (78774898021/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 7) (u := 5) (t := 8)
    (D := 8) (ψ := (225106501/5000000000 : ℝ)) half_10_12_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_10_12_bounds3 l).1) (fun l => (half_10_12_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_10_12_total1, half_10_12_total2, half_10_12_total3, half_10_12_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_6) (SeedCompletionHigher9SimpleSeeds.degree9_half_8)
    (by simpa only [half_10_12_φ4, show (2:ℝ)*8=16 by norm_num] using half_10_12_hx4)
  exact h.weaken (by norm_num [half_10_12_total1, half_10_12_total2, half_10_12_total3, half_10_12_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_10_12_hx2 : SourcePowerBound
    (powerBoxCross 9 8 4 half_10_12_φ2) (93469315421/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (143409611/2000000000 : ℝ)) half_10_12_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_10_12_bounds2 l).1) (fun l => (half_10_12_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_10_12_total1, half_10_12_total2, half_10_12_total3, half_10_12_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_7) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_10_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_12_hx3)
  exact h.weaken (by norm_num [half_10_12_total1, half_10_12_total2, half_10_12_total3, half_10_12_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_10_12_hx1 : SourcePowerBound
    (powerBoxCross 9 9 2 half_10_12_φ1) (112493986679/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (821568477/10000000000 : ℝ)) half_10_12_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_10_12_bounds1 l).1) (fun l => (half_10_12_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_10_12_total1, half_10_12_total2, half_10_12_total3, half_10_12_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_11)
    (by simpa only [half_10_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_12_hx2)
  exact h.weaken (by norm_num [half_10_12_total1, half_10_12_total2, half_10_12_total3, half_10_12_total4, parameterExponent, curveLoss, dyadicExponent])

theorem half_10_12 : AdmissibleExponent 9 20 (127463434667/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 8) (ψ := (220138941/2500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_10_12_φ1] using half_10_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_12_total1, half_10_12_total2, half_10_12_total3, half_10_12_total4, parameterExponent, curveLoss, dyadicExponent])

end Waring.SeedCompletionAlternate9Seeds
