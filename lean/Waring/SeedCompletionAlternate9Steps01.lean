import Waring.SeedCompletionAlternate9Arithmetic

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionAlternate9Seeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges SeedCompletionDivisorPowerScales
open PolicyCompletionSharpResidualSource

theorem half_10_00 : AdmissibleExponent 9 20 (129044467357/10000000000 : ℝ) := by
  have h := endpoint_admissible (s := 8) (by norm_num : 0 < (9 : ℕ))
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_11_00 : AdmissibleExponent 9 22 (146928415429/10000000000 : ℝ) := by
  have h := endpoint_admissible (s := 9) (by norm_num : 0 < (9 : ℕ))
    (half_10_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_12_00 : AdmissibleExponent 9 24 (82523740191/5000000000 : ℝ) := by
  have h := endpoint_admissible (s := 10) (by norm_num : 0 < (9 : ℕ))
    (half_11_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_13_00 : AdmissibleExponent 9 26 (91687769059/5000000000 : ℝ) := by
  have h := endpoint_admissible (s := 11) (by norm_num : 0 < (9 : ℕ))
    (half_12_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_14_00 : AdmissibleExponent 9 28 (12618085451/625000000 : ℝ) := by
  have h := endpoint_admissible (s := 12) (by norm_num : 0 < (9 : ℕ))
    (half_13_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_15_00 : AdmissibleExponent 9 30 (44113665283/2000000000 : ℝ) := by
  have h := endpoint_admissible (s := 13) (by norm_num : 0 < (9 : ℕ))
    (half_14_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_16_00 : AdmissibleExponent 9 32 (9575762717/400000000 : ℝ) := by
  have h := endpoint_admissible (s := 14) (by norm_num : 0 < (9 : ℕ))
    (half_15_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_17_00 : AdmissibleExponent 9 34 (1291751413/50000000 : ℝ) := by
  have h := endpoint_admissible (s := 15) (by norm_num : 0 < (9 : ℕ))
    (half_16_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_18_00 : AdmissibleExponent 9 36 (277422473423/10000000000 : ℝ) := by
  have h := endpoint_admissible (s := 16) (by norm_num : 0 < (9 : ℕ))
    (half_17_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_19_00 : AdmissibleExponent 9 38 (148298877077/5000000000 : ℝ) := by
  have h := endpoint_admissible (s := 17) (by norm_num : 0 < (9 : ℕ))
    (half_18_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_20_00 : AdmissibleExponent 9 40 (7896616759/250000000 : ℝ) := by
  have h := endpoint_admissible (s := 18) (by norm_num : 0 < (9 : ℕ))
    (half_19_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_21_00 : AdmissibleExponent 9 42 (1047540751/31250000 : ℝ) := by
  have h := endpoint_admissible (s := 19) (by norm_num : 0 < (9 : ℕ))
    (half_20_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

theorem half_22_00 : AdmissibleExponent 9 44 (177316906809/5000000000 : ℝ) := by
  have h := endpoint_admissible (s := 20) (by norm_num : 0 < (9 : ℕ))
    (half_21_00) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_10_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (240028393/2500000000 : ℝ)

private theorem half_10_01_total1 : total half_10_01_φ1=(240028393/2500000000 : ℝ) := by
  norm_num [half_10_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_10_01_bounds1 : ∀ l,0≤half_10_01_φ1 l ∧ half_10_01_φ1 l≤1 ∧
    0≤shiftExponents 9 half_10_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (240028393/2500000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_10_01_φ2 : Fin 2 → ℝ := Fin.snoc half_10_01_φ1 (51426259/625000000 : ℝ)

private theorem half_10_01_total2 : total half_10_01_φ2=(445733429/2500000000 : ℝ) := by
  change total (Fin.snoc half_10_01_φ1 (51426259/625000000 : ℝ))=(445733429/2500000000 : ℝ)
  rw [alternate_total_snoc,half_10_01_total1]
  norm_num

private theorem half_10_01_bounds2 : ∀ l,0≤half_10_01_φ2 l ∧ half_10_01_φ2 l≤1 ∧
    0≤shiftExponents 9 half_10_01_φ2 l :=
  alternate_bounds_snoc half_10_01_φ1 (51426259/625000000 : ℝ) half_10_01_bounds1 (by norm_num)

private def half_10_01_φ3 : Fin 3 → ℝ := Fin.snoc half_10_01_φ2 (721858387/10000000000 : ℝ)

private theorem half_10_01_total3 : total half_10_01_φ3=(2504792103/10000000000 : ℝ) := by
  change total (Fin.snoc half_10_01_φ2 (721858387/10000000000 : ℝ))=(2504792103/10000000000 : ℝ)
  rw [alternate_total_snoc,half_10_01_total2]
  norm_num

private theorem half_10_01_bounds3 : ∀ l,0≤half_10_01_φ3 l ∧ half_10_01_φ3 l≤1 ∧
    0≤shiftExponents 9 half_10_01_φ3 l :=
  alternate_bounds_snoc half_10_01_φ2 (721858387/10000000000 : ℝ) half_10_01_bounds2 (by norm_num)

private def half_10_01_φ4 : Fin 4 → ℝ := Fin.snoc half_10_01_φ3 (58477963/1250000000 : ℝ)

private theorem half_10_01_total4 : total half_10_01_φ4=(2972615807/10000000000 : ℝ) := by
  change total (Fin.snoc half_10_01_φ3 (58477963/1250000000 : ℝ))=(2972615807/10000000000 : ℝ)
  rw [alternate_total_snoc,half_10_01_total3]
  norm_num

private theorem half_10_01_bounds4 : ∀ l,0≤half_10_01_φ4 l ∧ half_10_01_φ4 l≤1 ∧
    0≤shiftExponents 9 half_10_01_φ4 l :=
  alternate_bounds_snoc half_10_01_φ3 (58477963/1250000000 : ℝ) half_10_01_bounds3 (by norm_num)

private theorem half_10_01_prefix : PrefixCondition 9 half_10_01_φ4 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_10_01_φ1, half_10_01_φ2, half_10_01_φ3, half_10_01_φ4, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_10_01_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 16 half_10_01_φ4) (8582152579/1250000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 9) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_01_φ4
    (fun i => (half_10_01_bounds4 i).1) (fun i => (half_10_01_bounds4 i).2.1)
    (fun i => (half_10_01_bounds4 i).2.2) half_10_01_prefix
  convert h using 1 <;> norm_num [half_10_01_total1, half_10_01_total2, half_10_01_total3, half_10_01_total4, parameterExponent, curveLoss, dyadicExponent]

private theorem half_10_01_hx4 : SourcePowerBound
    (powerBoxCross 9 6 16 half_10_01_φ4) (33891084377/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 6) (r := 2) (v := 0) (w := 8) (D := 16)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_10_01_φ4 (by norm_num [half_10_01_total1, half_10_01_total2, half_10_01_total3, half_10_01_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_10_01_total1, half_10_01_total2, half_10_01_total3, half_10_01_total4, parameterExponent, curveLoss, dyadicExponent]) half_10_01_hF2
    (admissibleExponent_zero 9) (SeedCompletionHigher9SimpleSeeds.degree9_half_8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_01_total1, half_10_01_total2, half_10_01_total3, half_10_01_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_10_01_hx3 : SourcePowerBound
    (powerBoxCross 9 7 8 half_10_01_φ3) (38718330543/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 7) (u := 5) (t := 8)
    (D := 8) (ψ := (58477963/1250000000 : ℝ)) half_10_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_10_01_bounds3 l).1) (fun l => (half_10_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_10_01_total1, half_10_01_total2, half_10_01_total3, half_10_01_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_6) (SeedCompletionHigher9SimpleSeeds.degree9_half_8)
    (by simpa only [half_10_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_10_01_hx4)
  exact h.weaken (by norm_num [half_10_01_total1, half_10_01_total2, half_10_01_total3, half_10_01_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_10_01_hx2 : SourcePowerBound
    (powerBoxCross 9 8 4 half_10_01_φ2) (287681301/31250000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (721858387/10000000000 : ℝ)) half_10_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_10_01_bounds2 l).1) (fun l => (half_10_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_10_01_total1, half_10_01_total2, half_10_01_total3, half_10_01_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_7) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_10_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_01_hx3)
  exact h.weaken (by norm_num [half_10_01_total1, half_10_01_total2, half_10_01_total3, half_10_01_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_10_01_hx1 : SourcePowerBound
    (powerBoxCross 9 9 2 half_10_01_φ1) (55843535703/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (51426259/625000000 : ℝ)) half_10_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_10_01_bounds1 l).1) (fun l => (half_10_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_10_01_total1, half_10_01_total2, half_10_01_total3, half_10_01_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_00)
    (by simpa only [half_10_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_01_hx2)
  exact h.weaken (by norm_num [half_10_01_total1, half_10_01_total2, half_10_01_total3, half_10_01_total4, parameterExponent, curveLoss, dyadicExponent])

theorem half_10_01 : AdmissibleExponent 9 20 (12800900213/1000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 8) (ψ := (240028393/2500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_10_01_φ1] using half_10_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_01_total1, half_10_01_total2, half_10_01_total3, half_10_01_total4, parameterExponent, curveLoss, dyadicExponent])

theorem chord_1 : AdmissibleExponent 9 22 (73232257063/5000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 22) (t := (2/3 : ℝ))
    (half_10_01) (half_13_00)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_11_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (494762063/5000000000 : ℝ)

private theorem half_11_01_total1 : total half_11_01_φ1=(494762063/5000000000 : ℝ) := by
  norm_num [half_11_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_11_01_bounds1 : ∀ l,0≤half_11_01_φ1 l ∧ half_11_01_φ1 l≤1 ∧
    0≤shiftExponents 9 half_11_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (494762063/5000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_11_01_φ2 : Fin 2 → ℝ := Fin.snoc half_11_01_φ1 (44659817/500000000 : ℝ)

private theorem half_11_01_total2 : total half_11_01_φ2=(941360233/5000000000 : ℝ) := by
  change total (Fin.snoc half_11_01_φ1 (44659817/500000000 : ℝ))=(941360233/5000000000 : ℝ)
  rw [alternate_total_snoc,half_11_01_total1]
  norm_num

private theorem half_11_01_bounds2 : ∀ l,0≤half_11_01_φ2 l ∧ half_11_01_φ2 l≤1 ∧
    0≤shiftExponents 9 half_11_01_φ2 l :=
  alternate_bounds_snoc half_11_01_φ1 (44659817/500000000 : ℝ) half_11_01_bounds1 (by norm_num)

private def half_11_01_φ3 : Fin 3 → ℝ := Fin.snoc half_11_01_φ2 (199532783/2500000000 : ℝ)

private theorem half_11_01_total3 : total half_11_01_φ3=(1340425799/5000000000 : ℝ) := by
  change total (Fin.snoc half_11_01_φ2 (199532783/2500000000 : ℝ))=(1340425799/5000000000 : ℝ)
  rw [alternate_total_snoc,half_11_01_total2]
  norm_num

private theorem half_11_01_bounds3 : ∀ l,0≤half_11_01_φ3 l ∧ half_11_01_φ3 l≤1 ∧
    0≤shiftExponents 9 half_11_01_φ3 l :=
  alternate_bounds_snoc half_11_01_φ2 (199532783/2500000000 : ℝ) half_11_01_bounds2 (by norm_num)

private def half_11_01_φ4 : Fin 4 → ℝ := Fin.snoc half_11_01_φ3 (164209909/2500000000 : ℝ)

private theorem half_11_01_total4 : total half_11_01_φ4=(1668845617/5000000000 : ℝ) := by
  change total (Fin.snoc half_11_01_φ3 (164209909/2500000000 : ℝ))=(1668845617/5000000000 : ℝ)
  rw [alternate_total_snoc,half_11_01_total3]
  norm_num

private theorem half_11_01_bounds4 : ∀ l,0≤half_11_01_φ4 l ∧ half_11_01_φ4 l≤1 ∧
    0≤shiftExponents 9 half_11_01_φ4 l :=
  alternate_bounds_snoc half_11_01_φ3 (164209909/2500000000 : ℝ) half_11_01_bounds3 (by norm_num)

private theorem half_11_01_prefix : PrefixCondition 9 half_11_01_φ4 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_11_01_φ1, half_11_01_φ2, half_11_01_φ3, half_11_01_φ4, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_11_01_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 16 half_11_01_φ4) (3743463149/625000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_11_01_φ4
    (fun i => (half_11_01_bounds4 i).1) (fun i => (half_11_01_bounds4 i).2.1)
    (fun i => (half_11_01_bounds4 i).2.2) half_11_01_prefix
  convert h using 1 <;> norm_num [half_11_01_total1, half_11_01_total2, half_11_01_total3, half_11_01_total4, parameterExponent, curveLoss, dyadicExponent]

private theorem half_11_01_hx4 : SourcePowerBound
    (powerBoxCross 9 7 16 half_11_01_φ4) (73412136321/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 7) (r := 2) (v := 9) (w := 10) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_11_01_φ4 (by norm_num [half_11_01_total1, half_11_01_total2, half_11_01_total3, half_11_01_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_11_01_total1, half_11_01_total2, half_11_01_total3, half_11_01_total4, parameterExponent, curveLoss, dyadicExponent]) half_11_01_hF2
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_10_01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_01_total1, half_11_01_total2, half_11_01_total3, half_11_01_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_11_01_hx3 : SourcePowerBound
    (powerBoxCross 9 8 8 half_11_01_φ3) (86028934371/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (164209909/2500000000 : ℝ)) half_11_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_11_01_bounds3 l).1) (fun l => (half_11_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_11_01_total1, half_11_01_total2, half_11_01_total3, half_11_01_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_7) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_11_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_01_hx4)
  exact h.weaken (by norm_num [half_11_01_total1, half_11_01_total2, half_11_01_total3, half_11_01_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_11_01_hx2 : SourcePowerBound
    (powerBoxCross 9 9 4 half_11_01_φ2) (10342381147/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (199532783/2500000000 : ℝ)) half_11_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_11_01_bounds2 l).1) (fun l => (half_11_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_11_01_total1, half_11_01_total2, half_11_01_total3, half_11_01_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_01)
    (by simpa only [half_11_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_01_hx3)
  exact h.weaken (by norm_num [half_11_01_total1, half_11_01_total2, half_11_01_total3, half_11_01_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_11_01_hx1 : SourcePowerBound
    (powerBoxCross 9 10 2 half_11_01_φ1) (31582931667/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (44659817/500000000 : ℝ)) half_11_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_11_01_bounds1 l).1) (fun l => (half_11_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_11_01_total1, half_11_01_total2, half_11_01_total3, half_11_01_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (chord_1)
    (by simpa only [half_11_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_01_hx2)
  exact h.weaken (by norm_num [half_11_01_total1, half_11_01_total2, half_11_01_total3, half_11_01_total4, parameterExponent, curveLoss, dyadicExponent])

theorem half_11_01 : AdmissibleExponent 9 22 (72566342531/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 9) (ψ := (494762063/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_10_01)
    (by simpa only [half_11_01_φ1] using half_11_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_01_total1, half_11_01_total2, half_11_01_total3, half_11_01_total4, parameterExponent, curveLoss, dyadicExponent])

theorem chord_3 : AdmissibleExponent 9 24 (819924808173/50000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 24) (t := (4/5 : ℝ))
    (half_11_01) (half_16_00)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_12_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1005690269/10000000000 : ℝ)

private theorem half_12_01_total1 : total half_12_01_φ1=(1005690269/10000000000 : ℝ) := by
  norm_num [half_12_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_12_01_bounds1 : ∀ l,0≤half_12_01_φ1 l ∧ half_12_01_φ1 l≤1 ∧
    0≤shiftExponents 9 half_12_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (1005690269/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_12_01_φ2 : Fin 2 → ℝ := Fin.snoc half_12_01_φ1 (909512909/10000000000 : ℝ)

private theorem half_12_01_total2 : total half_12_01_φ2=(957601589/5000000000 : ℝ) := by
  change total (Fin.snoc half_12_01_φ1 (909512909/10000000000 : ℝ))=(957601589/5000000000 : ℝ)
  rw [alternate_total_snoc,half_12_01_total1]
  norm_num

private theorem half_12_01_bounds2 : ∀ l,0≤half_12_01_φ2 l ∧ half_12_01_φ2 l≤1 ∧
    0≤shiftExponents 9 half_12_01_φ2 l :=
  alternate_bounds_snoc half_12_01_φ1 (909512909/10000000000 : ℝ) half_12_01_bounds1 (by norm_num)

private def half_12_01_φ3 : Fin 3 → ℝ := Fin.snoc half_12_01_φ2 (865460123/10000000000 : ℝ)

private theorem half_12_01_total3 : total half_12_01_φ3=(2780663301/10000000000 : ℝ) := by
  change total (Fin.snoc half_12_01_φ2 (865460123/10000000000 : ℝ))=(2780663301/10000000000 : ℝ)
  rw [alternate_total_snoc,half_12_01_total2]
  norm_num

private theorem half_12_01_bounds3 : ∀ l,0≤half_12_01_φ3 l ∧ half_12_01_φ3 l≤1 ∧
    0≤shiftExponents 9 half_12_01_φ3 l :=
  alternate_bounds_snoc half_12_01_φ2 (865460123/10000000000 : ℝ) half_12_01_bounds2 (by norm_num)

private def half_12_01_φ4 : Fin 4 → ℝ := Fin.snoc half_12_01_φ3 (736896911/10000000000 : ℝ)

private theorem half_12_01_total4 : total half_12_01_φ4=(879390053/2500000000 : ℝ) := by
  change total (Fin.snoc half_12_01_φ3 (736896911/10000000000 : ℝ))=(879390053/2500000000 : ℝ)
  rw [alternate_total_snoc,half_12_01_total3]
  norm_num

private theorem half_12_01_bounds4 : ∀ l,0≤half_12_01_φ4 l ∧ half_12_01_φ4 l≤1 ∧
    0≤shiftExponents 9 half_12_01_φ4 l :=
  alternate_bounds_snoc half_12_01_φ3 (736896911/10000000000 : ℝ) half_12_01_bounds3 (by norm_num)

private def half_12_01_φ5 : Fin 5 → ℝ := Fin.snoc half_12_01_φ4 (478915957/10000000000 : ℝ)

private theorem half_12_01_total5 : total half_12_01_φ5=(3996476169/10000000000 : ℝ) := by
  change total (Fin.snoc half_12_01_φ4 (478915957/10000000000 : ℝ))=(3996476169/10000000000 : ℝ)
  rw [alternate_total_snoc,half_12_01_total4]
  norm_num

private theorem half_12_01_bounds5 : ∀ l,0≤half_12_01_φ5 l ∧ half_12_01_φ5 l≤1 ∧
    0≤shiftExponents 9 half_12_01_φ5 l :=
  alternate_bounds_snoc half_12_01_φ4 (478915957/10000000000 : ℝ) half_12_01_bounds4 (by norm_num)

private theorem half_12_01_prefix : PrefixCondition 9 half_12_01_φ5 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_12_01_φ1, half_12_01_φ2, half_12_01_φ3, half_12_01_φ4, half_12_01_φ5, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_12_01_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 32 half_12_01_φ5) (9260571493/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_12_01_φ5
    (fun i => (half_12_01_bounds5 i).1) (fun i => (half_12_01_bounds5 i).2.1)
    (fun i => (half_12_01_bounds5 i).2.2) half_12_01_prefix
  convert h using 1 <;> norm_num [half_12_01_total1, half_12_01_total2, half_12_01_total3, half_12_01_total4, half_12_01_total5, parameterExponent, curveLoss, dyadicExponent]

private theorem half_12_01_hx5 : SourcePowerBound
    (powerBoxCross 9 7 32 half_12_01_φ5) (71180910239/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 7) (r := 2) (v := 9) (w := 10) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_12_01_φ5 (by norm_num [half_12_01_total1, half_12_01_total2, half_12_01_total3, half_12_01_total4, half_12_01_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_12_01_total1, half_12_01_total2, half_12_01_total3, half_12_01_total4, half_12_01_total5, parameterExponent, curveLoss, dyadicExponent]) half_12_01_hF2
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_10_01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_01_total1, half_12_01_total2, half_12_01_total3, half_12_01_total4, half_12_01_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_01_hx4 : SourcePowerBound
    (powerBoxCross 9 8 16 half_12_01_φ4) (80748469017/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 8) (u := 6) (t := 9)
    (D := 16) (ψ := (478915957/10000000000 : ℝ)) half_12_01_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_01_bounds4 l).1) (fun l => (half_12_01_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_01_total1, half_12_01_total2, half_12_01_total3, half_12_01_total4, half_12_01_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_7) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_12_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_12_01_hx5)
  exact h.weaken (by norm_num [half_12_01_total1, half_12_01_total2, half_12_01_total3, half_12_01_total4, half_12_01_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_01_hx3 : SourcePowerBound
    (powerBoxCross 9 9 8 half_12_01_φ3) (95985312481/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (736896911/10000000000 : ℝ)) half_12_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_01_bounds3 l).1) (fun l => (half_12_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_01_total1, half_12_01_total2, half_12_01_total3, half_12_01_total4, half_12_01_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_01)
    (by simpa only [half_12_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_01_hx4)
  exact h.weaken (by norm_num [half_12_01_total1, half_12_01_total2, half_12_01_total3, half_12_01_total4, half_12_01_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_01_hx2 : SourcePowerBound
    (powerBoxCross 9 10 4 half_12_01_φ2) (58178334061/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (865460123/10000000000 : ℝ)) half_12_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_01_bounds2 l).1) (fun l => (half_12_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_01_total1, half_12_01_total2, half_12_01_total3, half_12_01_total4, half_12_01_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_01)
    (by simpa only [half_12_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_01_hx3)
  exact h.weaken (by norm_num [half_12_01_total1, half_12_01_total2, half_12_01_total3, half_12_01_total4, half_12_01_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_01_hx1 : SourcePowerBound
    (powerBoxCross 9 11 2 half_12_01_φ1) (141542522429/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (909512909/10000000000 : ℝ)) half_12_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_01_bounds1 l).1) (fun l => (half_12_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_01_total1, half_12_01_total2, half_12_01_total3, half_12_01_total4, half_12_01_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_01) (chord_3)
    (by simpa only [half_12_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_01_hx2)
  exact h.weaken (by norm_num [half_12_01_total1, half_12_01_total2, half_12_01_total3, half_12_01_total4, half_12_01_total5, parameterExponent, curveLoss, dyadicExponent])

theorem half_12_01 : AdmissibleExponent 9 24 (81331009039/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 10) (ψ := (1005690269/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_11_01)
    (by simpa only [half_12_01_φ1] using half_12_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_01_total1, half_12_01_total2, half_12_01_total3, half_12_01_total4, half_12_01_total5, parameterExponent, curveLoss, dyadicExponent])

theorem chord_7 : AdmissibleExponent 9 26 (363577521271/20000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 26) (t := (5/6 : ℝ))
    (half_12_01) (half_18_00)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_13_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1022767337/10000000000 : ℝ)

private theorem half_13_01_total1 : total half_13_01_φ1=(1022767337/10000000000 : ℝ) := by
  norm_num [half_13_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_13_01_bounds1 : ∀ l,0≤half_13_01_φ1 l ∧ half_13_01_φ1 l≤1 ∧
    0≤shiftExponents 9 half_13_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (1022767337/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_13_01_φ2 : Fin 2 → ℝ := Fin.snoc half_13_01_φ1 (232938111/2500000000 : ℝ)

private theorem half_13_01_total2 : total half_13_01_φ2=(1954519781/10000000000 : ℝ) := by
  change total (Fin.snoc half_13_01_φ1 (232938111/2500000000 : ℝ))=(1954519781/10000000000 : ℝ)
  rw [alternate_total_snoc,half_13_01_total1]
  norm_num

private theorem half_13_01_bounds2 : ∀ l,0≤half_13_01_φ2 l ∧ half_13_01_φ2 l≤1 ∧
    0≤shiftExponents 9 half_13_01_φ2 l :=
  alternate_bounds_snoc half_13_01_φ1 (232938111/2500000000 : ℝ) half_13_01_bounds1 (by norm_num)

private def half_13_01_φ3 : Fin 3 → ℝ := Fin.snoc half_13_01_φ2 (895275689/10000000000 : ℝ)

private theorem half_13_01_total3 : total half_13_01_φ3=(284979547/1000000000 : ℝ) := by
  change total (Fin.snoc half_13_01_φ2 (895275689/10000000000 : ℝ))=(284979547/1000000000 : ℝ)
  rw [alternate_total_snoc,half_13_01_total2]
  norm_num

private theorem half_13_01_bounds3 : ∀ l,0≤half_13_01_φ3 l ∧ half_13_01_φ3 l≤1 ∧
    0≤shiftExponents 9 half_13_01_φ3 l :=
  alternate_bounds_snoc half_13_01_φ2 (895275689/10000000000 : ℝ) half_13_01_bounds2 (by norm_num)

private def half_13_01_φ4 : Fin 4 → ℝ := Fin.snoc half_13_01_φ3 (104430611/1250000000 : ℝ)

private theorem half_13_01_total4 : total half_13_01_φ4=(1842620179/5000000000 : ℝ) := by
  change total (Fin.snoc half_13_01_φ3 (104430611/1250000000 : ℝ))=(1842620179/5000000000 : ℝ)
  rw [alternate_total_snoc,half_13_01_total3]
  norm_num

private theorem half_13_01_bounds4 : ∀ l,0≤half_13_01_φ4 l ∧ half_13_01_φ4 l≤1 ∧
    0≤shiftExponents 9 half_13_01_φ4 l :=
  alternate_bounds_snoc half_13_01_φ3 (104430611/1250000000 : ℝ) half_13_01_bounds3 (by norm_num)

private def half_13_01_φ5 : Fin 5 → ℝ := Fin.snoc half_13_01_φ4 (669373301/10000000000 : ℝ)

private theorem half_13_01_total5 : total half_13_01_φ5=(4354613659/10000000000 : ℝ) := by
  change total (Fin.snoc half_13_01_φ4 (669373301/10000000000 : ℝ))=(4354613659/10000000000 : ℝ)
  rw [alternate_total_snoc,half_13_01_total4]
  norm_num

private theorem half_13_01_bounds5 : ∀ l,0≤half_13_01_φ5 l ∧ half_13_01_φ5 l≤1 ∧
    0≤shiftExponents 9 half_13_01_φ5 l :=
  alternate_bounds_snoc half_13_01_φ4 (669373301/10000000000 : ℝ) half_13_01_bounds4 (by norm_num)

private theorem half_13_01_prefix : PrefixCondition 9 half_13_01_φ5 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_13_01_φ1, half_13_01_φ2, half_13_01_φ3, half_13_01_φ4, half_13_01_φ5, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_13_01_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 32 half_13_01_φ5) (8186159023/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_13_01_φ5
    (fun i => (half_13_01_bounds5 i).1) (fun i => (half_13_01_bounds5 i).2.1)
    (fun i => (half_13_01_bounds5 i).2.2) half_13_01_prefix
  convert h using 1 <;> norm_num [half_13_01_total1, half_13_01_total2, half_13_01_total3, half_13_01_total4, half_13_01_total5, parameterExponent, curveLoss, dyadicExponent]

private theorem half_13_01_hx5 : SourcePowerBound
    (powerBoxCross 9 8 32 half_13_01_φ5) (9425666093/1250000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 8) (r := 2) (v := 10) (w := 11) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_13_01_φ5 (by norm_num [half_13_01_total1, half_13_01_total2, half_13_01_total3, half_13_01_total4, half_13_01_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_13_01_total1, half_13_01_total2, half_13_01_total3, half_13_01_total4, half_13_01_total5, parameterExponent, curveLoss, dyadicExponent]) half_13_01_hF2
    (half_10_01) (half_11_01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_01_total1, half_13_01_total2, half_13_01_total3, half_13_01_total4, half_13_01_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_01_hx4 : SourcePowerBound
    (powerBoxCross 9 9 16 half_13_01_φ4) (44199653361/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (669373301/10000000000 : ℝ)) half_13_01_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_01_bounds4 l).1) (fun l => (half_13_01_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_01_total1, half_13_01_total2, half_13_01_total3, half_13_01_total4, half_13_01_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_01)
    (by simpa only [half_13_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_01_hx5)
  exact h.weaken (by norm_num [half_13_01_total1, half_13_01_total2, half_13_01_total3, half_13_01_total4, half_13_01_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_01_hx3 : SourcePowerBound
    (powerBoxCross 9 10 8 half_13_01_φ3) (106788172139/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (104430611/1250000000 : ℝ)) half_13_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_01_bounds3 l).1) (fun l => (half_13_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_01_total1, half_13_01_total2, half_13_01_total3, half_13_01_total4, half_13_01_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_01)
    (by simpa only [half_13_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_01_hx4)
  exact h.weaken (by norm_num [half_13_01_total1, half_13_01_total2, half_13_01_total3, half_13_01_total4, half_13_01_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_01_hx2 : SourcePowerBound
    (powerBoxCross 9 11 4 half_13_01_φ2) (129515828433/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (895275689/10000000000 : ℝ)) half_13_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_01_bounds2 l).1) (fun l => (half_13_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_01_total1, half_13_01_total2, half_13_01_total3, half_13_01_total4, half_13_01_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_01) (half_12_01)
    (by simpa only [half_13_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_01_hx3)
  exact h.weaken (by norm_num [half_13_01_total1, half_13_01_total2, half_13_01_total3, half_13_01_total4, half_13_01_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_01_hx1 : SourcePowerBound
    (powerBoxCross 9 12 2 half_13_01_φ1) (78524122759/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (232938111/2500000000 : ℝ)) half_13_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_01_bounds1 l).1) (fun l => (half_13_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_01_total1, half_13_01_total2, half_13_01_total3, half_13_01_total4, half_13_01_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_01) (chord_7)
    (by simpa only [half_13_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_01_hx2)
  exact h.weaken (by norm_num [half_13_01_total1, half_13_01_total2, half_13_01_total3, half_13_01_total4, half_13_01_total5, parameterExponent, curveLoss, dyadicExponent])

theorem half_13_01 : AdmissibleExponent 9 26 (180571894269/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 11) (ψ := (1022767337/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_12_01)
    (by simpa only [half_13_01_φ1] using half_13_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_01_total1, half_13_01_total2, half_13_01_total3, half_13_01_total4, half_13_01_total5, parameterExponent, curveLoss, dyadicExponent])

theorem chord_12 : AdmissibleExponent 9 28 (699648017987/35000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 28) (t := (6/7 : ℝ))
    (half_13_01) (half_20_00)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_14_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (64754343/625000000 : ℝ)

private theorem half_14_01_total1 : total half_14_01_φ1=(64754343/625000000 : ℝ) := by
  norm_num [half_14_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_14_01_bounds1 : ∀ l,0≤half_14_01_φ1 l ∧ half_14_01_φ1 l≤1 ∧
    0≤shiftExponents 9 half_14_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (64754343/625000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_14_01_φ2 : Fin 2 → ℝ := Fin.snoc half_14_01_φ1 (954054801/10000000000 : ℝ)

private theorem half_14_01_total2 : total half_14_01_φ2=(1990124289/10000000000 : ℝ) := by
  change total (Fin.snoc half_14_01_φ1 (954054801/10000000000 : ℝ))=(1990124289/10000000000 : ℝ)
  rw [alternate_total_snoc,half_14_01_total1]
  norm_num

private theorem half_14_01_bounds2 : ∀ l,0≤half_14_01_φ2 l ∧ half_14_01_φ2 l≤1 ∧
    0≤shiftExponents 9 half_14_01_φ2 l :=
  alternate_bounds_snoc half_14_01_φ1 (954054801/10000000000 : ℝ) half_14_01_bounds1 (by norm_num)

private def half_14_01_φ3 : Fin 3 → ℝ := Fin.snoc half_14_01_φ2 (458689889/5000000000 : ℝ)

private theorem half_14_01_total3 : total half_14_01_φ3=(2907504067/10000000000 : ℝ) := by
  change total (Fin.snoc half_14_01_φ2 (458689889/5000000000 : ℝ))=(2907504067/10000000000 : ℝ)
  rw [alternate_total_snoc,half_14_01_total2]
  norm_num

private theorem half_14_01_bounds3 : ∀ l,0≤half_14_01_φ3 l ∧ half_14_01_φ3 l≤1 ∧
    0≤shiftExponents 9 half_14_01_φ3 l :=
  alternate_bounds_snoc half_14_01_φ2 (458689889/5000000000 : ℝ) half_14_01_bounds2 (by norm_num)

private def half_14_01_φ4 : Fin 4 → ℝ := Fin.snoc half_14_01_φ3 (172941869/2000000000 : ℝ)

private theorem half_14_01_total4 : total half_14_01_φ4=(943053353/2500000000 : ℝ) := by
  change total (Fin.snoc half_14_01_φ3 (172941869/2000000000 : ℝ))=(943053353/2500000000 : ℝ)
  rw [alternate_total_snoc,half_14_01_total3]
  norm_num

private theorem half_14_01_bounds4 : ∀ l,0≤half_14_01_φ4 l ∧ half_14_01_φ4 l≤1 ∧
    0≤shiftExponents 9 half_14_01_φ4 l :=
  alternate_bounds_snoc half_14_01_φ3 (172941869/2000000000 : ℝ) half_14_01_bounds3 (by norm_num)

private def half_14_01_φ5 : Fin 5 → ℝ := Fin.snoc half_14_01_φ4 (762472101/10000000000 : ℝ)

private theorem half_14_01_total5 : total half_14_01_φ5=(4534685513/10000000000 : ℝ) := by
  change total (Fin.snoc half_14_01_φ4 (762472101/10000000000 : ℝ))=(4534685513/10000000000 : ℝ)
  rw [alternate_total_snoc,half_14_01_total4]
  norm_num

private theorem half_14_01_bounds5 : ∀ l,0≤half_14_01_φ5 l ∧ half_14_01_φ5 l≤1 ∧
    0≤shiftExponents 9 half_14_01_φ5 l :=
  alternate_bounds_snoc half_14_01_φ4 (762472101/10000000000 : ℝ) half_14_01_bounds4 (by norm_num)

private def half_14_01_φ6 : Fin 6 → ℝ := Fin.snoc half_14_01_φ5 (119981143/2500000000 : ℝ)

private theorem half_14_01_total6 : total half_14_01_φ6=(1002922017/2000000000 : ℝ) := by
  change total (Fin.snoc half_14_01_φ5 (119981143/2500000000 : ℝ))=(1002922017/2000000000 : ℝ)
  rw [alternate_total_snoc,half_14_01_total5]
  norm_num

private theorem half_14_01_bounds6 : ∀ l,0≤half_14_01_φ6 l ∧ half_14_01_φ6 l≤1 ∧
    0≤shiftExponents 9 half_14_01_φ6 l :=
  alternate_bounds_snoc half_14_01_φ5 (119981143/2500000000 : ℝ) half_14_01_bounds5 (by norm_num)

private theorem half_14_01_prefix : PrefixCondition 9 half_14_01_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_14_01_φ1, half_14_01_φ2, half_14_01_φ3, half_14_01_φ4, half_14_01_φ5, half_14_01_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_14_01_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_14_01_φ6) (1991233949/250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_14_01_φ6
    (fun i => (half_14_01_bounds6 i).1) (fun i => (half_14_01_bounds6 i).2.1)
    (fun i => (half_14_01_bounds6 i).2.2) half_14_01_prefix
  convert h using 1 <;> norm_num [half_14_01_total1, half_14_01_total2, half_14_01_total3, half_14_01_total4, half_14_01_total5, half_14_01_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_14_01_hF1 : SourcePowerBound
    (paddedMoment 9 0 1 64 half_14_01_φ6) (747077983/250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_14_01_φ6
    (fun i => (half_14_01_bounds6 i).1) (fun i => (half_14_01_bounds6 i).2.1)
    (fun i => (half_14_01_bounds6 i).2.2) half_14_01_prefix
  convert h using 1 <;> norm_num [half_14_01_total1, half_14_01_total2, half_14_01_total3, half_14_01_total4, half_14_01_total5, half_14_01_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_14_01_hx6 : SourcePowerBound
    (powerBoxCross 9 8 64 half_14_01_φ6) (18020440321/2500000000 : ℝ) := by
  have h := full_B_cross_power (k := 9) (s := 8) (r := 1) (v := 2) (t := 11) (D := 64)
    (a := (1/22 : ℝ)) (b := (5/22 : ℝ)) (c := (8/11 : ℝ))
    (by norm_num) half_14_01_φ6 (by norm_num [half_14_01_total1, half_14_01_total2, half_14_01_total3, half_14_01_total4, half_14_01_total5, half_14_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_14_01_total1, half_14_01_total2, half_14_01_total3, half_14_01_total4, half_14_01_total5, half_14_01_total6, parameterExponent, curveLoss, dyadicExponent]) half_14_01_hF1 half_14_01_hF2
    (half_11_01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_01_total1, half_14_01_total2, half_14_01_total3, half_14_01_total4, half_14_01_total5, half_14_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_01_hx5 : SourcePowerBound
    (powerBoxCross 9 9 32 half_14_01_φ5) (81482045571/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 9) (u := 7) (t := 10)
    (D := 32) (ψ := (119981143/2500000000 : ℝ)) half_14_01_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_01_bounds5 l).1) (fun l => (half_14_01_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_01_total1, half_14_01_total2, half_14_01_total3, half_14_01_total4, half_14_01_total5, half_14_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_01)
    (by simpa only [half_14_01_φ6, show (2:ℝ)*32=64 by norm_num] using half_14_01_hx6)
  exact h.weaken (by norm_num [half_14_01_total1, half_14_01_total2, half_14_01_total3, half_14_01_total4, half_14_01_total5, half_14_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_01_hx4 : SourcePowerBound
    (powerBoxCross 9 10 16 half_14_01_φ4) (6082871967/625000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (762472101/10000000000 : ℝ)) half_14_01_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_01_bounds4 l).1) (fun l => (half_14_01_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_01_total1, half_14_01_total2, half_14_01_total3, half_14_01_total4, half_14_01_total5, half_14_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_01)
    (by simpa only [half_14_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_01_hx5)
  exact h.weaken (by norm_num [half_14_01_total1, half_14_01_total2, half_14_01_total3, half_14_01_total4, half_14_01_total5, half_14_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_01_hx3 : SourcePowerBound
    (powerBoxCross 9 11 8 half_14_01_φ3) (11793168333/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (172941869/2000000000 : ℝ)) half_14_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_01_bounds3 l).1) (fun l => (half_14_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_01_total1, half_14_01_total2, half_14_01_total3, half_14_01_total4, half_14_01_total5, half_14_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_01) (half_12_01)
    (by simpa only [half_14_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_01_hx4)
  exact h.weaken (by norm_num [half_14_01_total1, half_14_01_total2, half_14_01_total3, half_14_01_total4, half_14_01_total5, half_14_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_01_hx2 : SourcePowerBound
    (powerBoxCross 9 12 4 half_14_01_φ2) (71477876839/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (458689889/5000000000 : ℝ)) half_14_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_01_bounds2 l).1) (fun l => (half_14_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_01_total1, half_14_01_total2, half_14_01_total3, half_14_01_total4, half_14_01_total5, half_14_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_01) (half_13_01)
    (by simpa only [half_14_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_01_hx3)
  exact h.weaken (by norm_num [half_14_01_total1, half_14_01_total2, half_14_01_total3, half_14_01_total4, half_14_01_total5, half_14_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_01_hx1 : SourcePowerBound
    (powerBoxCross 9 13 2 half_14_01_φ1) (172899460757/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (954054801/10000000000 : ℝ)) half_14_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_01_bounds1 l).1) (fun l => (half_14_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_01_total1, half_14_01_total2, half_14_01_total3, half_14_01_total4, half_14_01_total5, half_14_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_01) (chord_12)
    (by simpa only [half_14_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_01_hx2)
  exact h.weaken (by norm_num [half_14_01_total1, half_14_01_total2, half_14_01_total3, half_14_01_total4, half_14_01_total5, half_14_01_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_14_01 : AdmissibleExponent 9 28 (198801197957/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 12) (ψ := (64754343/625000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_13_01)
    (by simpa only [half_14_01_φ1] using half_14_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_01_total1, half_14_01_total2, half_14_01_total3, half_14_01_total4, half_14_01_total5, half_14_01_total6, parameterExponent, curveLoss, dyadicExponent])

theorem chord_18 : AdmissibleExponent 9 30 (1746242199317/80000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 30) (t := (7/8 : ℝ))
    (half_14_01) (half_22_00)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_15_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (262014151/2500000000 : ℝ)

private theorem half_15_01_total1 : total half_15_01_φ1=(262014151/2500000000 : ℝ) := by
  norm_num [half_15_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_15_01_bounds1 : ∀ l,0≤half_15_01_φ1 l ∧ half_15_01_φ1 l≤1 ∧
    0≤shiftExponents 9 half_15_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (262014151/2500000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_15_01_φ2 : Fin 2 → ℝ := Fin.snoc half_15_01_φ1 (487625183/5000000000 : ℝ)

private theorem half_15_01_total2 : total half_15_01_φ2=(202330697/1000000000 : ℝ) := by
  change total (Fin.snoc half_15_01_φ1 (487625183/5000000000 : ℝ))=(202330697/1000000000 : ℝ)
  rw [alternate_total_snoc,half_15_01_total1]
  norm_num

private theorem half_15_01_bounds2 : ∀ l,0≤half_15_01_φ2 l ∧ half_15_01_φ2 l≤1 ∧
    0≤shiftExponents 9 half_15_01_φ2 l :=
  alternate_bounds_snoc half_15_01_φ1 (487625183/5000000000 : ℝ) half_15_01_bounds1 (by norm_num)

private def half_15_01_φ3 : Fin 3 → ℝ := Fin.snoc half_15_01_φ2 (943871161/10000000000 : ℝ)

private theorem half_15_01_total3 : total half_15_01_φ3=(2967178131/10000000000 : ℝ) := by
  change total (Fin.snoc half_15_01_φ2 (943871161/10000000000 : ℝ))=(2967178131/10000000000 : ℝ)
  rw [alternate_total_snoc,half_15_01_total2]
  norm_num

private theorem half_15_01_bounds3 : ∀ l,0≤half_15_01_φ3 l ∧ half_15_01_φ3 l≤1 ∧
    0≤shiftExponents 9 half_15_01_φ3 l :=
  alternate_bounds_snoc half_15_01_φ2 (943871161/10000000000 : ℝ) half_15_01_bounds2 (by norm_num)

private def half_15_01_φ4 : Fin 4 → ℝ := Fin.snoc half_15_01_φ3 (879102733/10000000000 : ℝ)

private theorem half_15_01_total4 : total half_15_01_φ4=(120196277/312500000 : ℝ) := by
  change total (Fin.snoc half_15_01_φ3 (879102733/10000000000 : ℝ))=(120196277/312500000 : ℝ)
  rw [alternate_total_snoc,half_15_01_total3]
  norm_num

private theorem half_15_01_bounds4 : ∀ l,0≤half_15_01_φ4 l ∧ half_15_01_φ4 l≤1 ∧
    0≤shiftExponents 9 half_15_01_φ4 l :=
  alternate_bounds_snoc half_15_01_φ3 (879102733/10000000000 : ℝ) half_15_01_bounds3 (by norm_num)

private def half_15_01_φ5 : Fin 5 → ℝ := Fin.snoc half_15_01_φ4 (769214891/10000000000 : ℝ)

private theorem half_15_01_total5 : total half_15_01_φ5=(923099151/2000000000 : ℝ) := by
  change total (Fin.snoc half_15_01_φ4 (769214891/10000000000 : ℝ))=(923099151/2000000000 : ℝ)
  rw [alternate_total_snoc,half_15_01_total4]
  norm_num

private theorem half_15_01_bounds5 : ∀ l,0≤half_15_01_φ5 l ∧ half_15_01_φ5 l≤1 ∧
    0≤shiftExponents 9 half_15_01_φ5 l :=
  alternate_bounds_snoc half_15_01_φ4 (769214891/10000000000 : ℝ) half_15_01_bounds4 (by norm_num)

private def half_15_01_φ6 : Fin 6 → ℝ := Fin.snoc half_15_01_φ5 (611036699/10000000000 : ℝ)

private theorem half_15_01_total6 : total half_15_01_φ6=(2613266227/5000000000 : ℝ) := by
  change total (Fin.snoc half_15_01_φ5 (611036699/10000000000 : ℝ))=(2613266227/5000000000 : ℝ)
  rw [alternate_total_snoc,half_15_01_total5]
  norm_num

private theorem half_15_01_bounds6 : ∀ l,0≤half_15_01_φ6 l ∧ half_15_01_φ6 l≤1 ∧
    0≤shiftExponents 9 half_15_01_φ6 l :=
  alternate_bounds_snoc half_15_01_φ5 (611036699/10000000000 : ℝ) half_15_01_bounds5 (by norm_num)

private theorem half_15_01_prefix : PrefixCondition 9 half_15_01_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_15_01_φ1, half_15_01_φ2, half_15_01_φ3, half_15_01_φ4, half_15_01_φ5, half_15_01_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_15_01_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_15_01_φ6) (4660201319/625000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_15_01_φ6
    (fun i => (half_15_01_bounds6 i).1) (fun i => (half_15_01_bounds6 i).2.1)
    (fun i => (half_15_01_bounds6 i).2.2) half_15_01_prefix
  convert h using 1 <;> norm_num [half_15_01_total1, half_15_01_total2, half_15_01_total3, half_15_01_total4, half_15_01_total5, half_15_01_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_15_01_hx6 : SourcePowerBound
    (powerBoxCross 9 9 64 half_15_01_φ6) (9609430637/1250000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 9) (r := 2) (v := 0) (w := 12) (D := 64)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_15_01_φ6 (by norm_num [half_15_01_total1, half_15_01_total2, half_15_01_total3, half_15_01_total4, half_15_01_total5, half_15_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_15_01_total1, half_15_01_total2, half_15_01_total3, half_15_01_total4, half_15_01_total5, half_15_01_total6, parameterExponent, curveLoss, dyadicExponent]) half_15_01_hF2
    (admissibleExponent_zero 9) (half_12_01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_01_total1, half_15_01_total2, half_15_01_total3, half_15_01_total4, half_15_01_total5, half_15_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_01_hx5 : SourcePowerBound
    (powerBoxCross 9 10 32 half_15_01_φ5) (8924292941/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 10) (u := 8) (t := 11)
    (D := 32) (ψ := (611036699/10000000000 : ℝ)) half_15_01_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_01_bounds5 l).1) (fun l => (half_15_01_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_01_total1, half_15_01_total2, half_15_01_total3, half_15_01_total4, half_15_01_total5, half_15_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_01)
    (by simpa only [half_15_01_φ6, show (2:ℝ)*32=64 by norm_num] using half_15_01_hx6)
  exact h.weaken (by norm_num [half_15_01_total1, half_15_01_total2, half_15_01_total3, half_15_01_total4, half_15_01_total5, half_15_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_01_hx4 : SourcePowerBound
    (powerBoxCross 9 11 16 half_15_01_φ4) (106592701381/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (769214891/10000000000 : ℝ)) half_15_01_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_01_bounds4 l).1) (fun l => (half_15_01_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_01_total1, half_15_01_total2, half_15_01_total3, half_15_01_total4, half_15_01_total5, half_15_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_01) (half_12_01)
    (by simpa only [half_15_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_01_hx5)
  exact h.weaken (by norm_num [half_15_01_total1, half_15_01_total2, half_15_01_total3, half_15_01_total4, half_15_01_total5, half_15_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_01_hx3 : SourcePowerBound
    (powerBoxCross 9 12 8 half_15_01_φ3) (129154715211/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (879102733/10000000000 : ℝ)) half_15_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_01_bounds3 l).1) (fun l => (half_15_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_01_total1, half_15_01_total2, half_15_01_total3, half_15_01_total4, half_15_01_total5, half_15_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_01) (half_13_01)
    (by simpa only [half_15_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_01_hx4)
  exact h.weaken (by norm_num [half_15_01_total1, half_15_01_total2, half_15_01_total3, half_15_01_total4, half_15_01_total5, half_15_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_01_hx2 : SourcePowerBound
    (powerBoxCross 9 13 4 half_15_01_φ2) (78313727291/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (943871161/10000000000 : ℝ)) half_15_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_01_bounds2 l).1) (fun l => (half_15_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_01_total1, half_15_01_total2, half_15_01_total3, half_15_01_total4, half_15_01_total5, half_15_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_01) (half_14_01)
    (by simpa only [half_15_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_01_hx3)
  exact h.weaken (by norm_num [half_15_01_total1, half_15_01_total2, half_15_01_total3, half_15_01_total4, half_15_01_total5, half_15_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_01_hx1 : SourcePowerBound
    (powerBoxCross 9 14 2 half_15_01_φ1) (7560550549/400000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (487625183/5000000000 : ℝ)) half_15_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_01_bounds1 l).1) (fun l => (half_15_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_01_total1, half_15_01_total2, half_15_01_total3, half_15_01_total4, half_15_01_total5, half_15_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_01) (chord_18)
    (by simpa only [half_15_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_01_hx2)
  exact h.weaken (by norm_num [half_15_01_total1, half_15_01_total2, half_15_01_total3, half_15_01_total4, half_15_01_total5, half_15_01_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_15_01 : AdmissibleExponent 9 30 (217311292033/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 13) (ψ := (262014151/2500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_14_01)
    (by simpa only [half_15_01_φ1] using half_15_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_01_total1, half_15_01_total2, half_15_01_total3, half_15_01_total4, half_15_01_total5, half_15_01_total6, parameterExponent, curveLoss, dyadicExponent])

theorem chord_25 : AdmissibleExponent 9 32 (207312695727/8750000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 32) (t := (6/7 : ℝ))
    (half_15_01) (half_22_00)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_16_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (530005699/5000000000 : ℝ)

private theorem half_16_01_total1 : total half_16_01_φ1=(530005699/5000000000 : ℝ) := by
  norm_num [half_16_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_16_01_bounds1 : ∀ l,0≤half_16_01_φ1 l ∧ half_16_01_φ1 l≤1 ∧
    0≤shiftExponents 9 half_16_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (530005699/5000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_16_01_φ2 : Fin 2 → ℝ := Fin.snoc half_16_01_φ1 (996342627/10000000000 : ℝ)

private theorem half_16_01_total2 : total half_16_01_φ2=(82254161/400000000 : ℝ) := by
  change total (Fin.snoc half_16_01_φ1 (996342627/10000000000 : ℝ))=(82254161/400000000 : ℝ)
  rw [alternate_total_snoc,half_16_01_total1]
  norm_num

private theorem half_16_01_bounds2 : ∀ l,0≤half_16_01_φ2 l ∧ half_16_01_φ2 l≤1 ∧
    0≤shiftExponents 9 half_16_01_φ2 l :=
  alternate_bounds_snoc half_16_01_φ1 (996342627/10000000000 : ℝ) half_16_01_bounds1 (by norm_num)

private def half_16_01_φ3 : Fin 3 → ℝ := Fin.snoc half_16_01_φ2 (970829819/10000000000 : ℝ)

private theorem half_16_01_total3 : total half_16_01_φ3=(756795961/2500000000 : ℝ) := by
  change total (Fin.snoc half_16_01_φ2 (970829819/10000000000 : ℝ))=(756795961/2500000000 : ℝ)
  rw [alternate_total_snoc,half_16_01_total2]
  norm_num

private theorem half_16_01_bounds3 : ∀ l,0≤half_16_01_φ3 l ∧ half_16_01_φ3 l≤1 ∧
    0≤shiftExponents 9 half_16_01_φ3 l :=
  alternate_bounds_snoc half_16_01_φ2 (970829819/10000000000 : ℝ) half_16_01_bounds2 (by norm_num)

private def half_16_01_φ4 : Fin 4 → ℝ := Fin.snoc half_16_01_φ3 (871602019/10000000000 : ℝ)

private theorem half_16_01_total4 : total half_16_01_φ4=(3898785863/10000000000 : ℝ) := by
  change total (Fin.snoc half_16_01_φ3 (871602019/10000000000 : ℝ))=(3898785863/10000000000 : ℝ)
  rw [alternate_total_snoc,half_16_01_total3]
  norm_num

private theorem half_16_01_bounds4 : ∀ l,0≤half_16_01_φ4 l ∧ half_16_01_φ4 l≤1 ∧
    0≤shiftExponents 9 half_16_01_φ4 l :=
  alternate_bounds_snoc half_16_01_φ3 (871602019/10000000000 : ℝ) half_16_01_bounds3 (by norm_num)

private def half_16_01_φ5 : Fin 5 → ℝ := Fin.snoc half_16_01_φ4 (381325883/5000000000 : ℝ)

private theorem half_16_01_total5 : total half_16_01_φ5=(4661437629/10000000000 : ℝ) := by
  change total (Fin.snoc half_16_01_φ4 (381325883/5000000000 : ℝ))=(4661437629/10000000000 : ℝ)
  rw [alternate_total_snoc,half_16_01_total4]
  norm_num

private theorem half_16_01_bounds5 : ∀ l,0≤half_16_01_φ5 l ∧ half_16_01_φ5 l≤1 ∧
    0≤shiftExponents 9 half_16_01_φ5 l :=
  alternate_bounds_snoc half_16_01_φ4 (381325883/5000000000 : ℝ) half_16_01_bounds4 (by norm_num)

private def half_16_01_φ6 : Fin 6 → ℝ := Fin.snoc half_16_01_φ5 (83415037/1250000000 : ℝ)

private theorem half_16_01_total6 : total half_16_01_φ6=(213150317/400000000 : ℝ) := by
  change total (Fin.snoc half_16_01_φ5 (83415037/1250000000 : ℝ))=(213150317/400000000 : ℝ)
  rw [alternate_total_snoc,half_16_01_total5]
  norm_num

private theorem half_16_01_bounds6 : ∀ l,0≤half_16_01_φ6 l ∧ half_16_01_φ6 l≤1 ∧
    0≤shiftExponents 9 half_16_01_φ6 l :=
  alternate_bounds_snoc half_16_01_φ5 (83415037/1250000000 : ℝ) half_16_01_bounds5 (by norm_num)

private theorem half_16_01_prefix : PrefixCondition 9 half_16_01_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_16_01_φ1, half_16_01_φ2, half_16_01_φ3, half_16_01_φ4, half_16_01_φ5, half_16_01_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_16_01_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_16_01_φ6) (360549049/50000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_16_01_φ6
    (fun i => (half_16_01_bounds6 i).1) (fun i => (half_16_01_bounds6 i).2.1)
    (fun i => (half_16_01_bounds6 i).2.2) half_16_01_prefix
  convert h using 1 <;> norm_num [half_16_01_total1, half_16_01_total2, half_16_01_total3, half_16_01_total4, half_16_01_total5, half_16_01_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_16_01_hx6 : SourcePowerBound
    (powerBoxCross 9 10 64 half_16_01_φ6) (41709208483/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 10) (r := 2) (v := 13) (w := 14) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_16_01_φ6 (by norm_num [half_16_01_total1, half_16_01_total2, half_16_01_total3, half_16_01_total4, half_16_01_total5, half_16_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_16_01_total1, half_16_01_total2, half_16_01_total3, half_16_01_total4, half_16_01_total5, half_16_01_total6, parameterExponent, curveLoss, dyadicExponent]) half_16_01_hF2
    (half_13_01) (half_14_01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_01_total1, half_16_01_total2, half_16_01_total3, half_16_01_total4, half_16_01_total5, half_16_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_01_hx5 : SourcePowerBound
    (powerBoxCross 9 11 32 half_16_01_φ5) (3912882689/400000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 11) (u := 9) (t := 12)
    (D := 32) (ψ := (83415037/1250000000 : ℝ)) half_16_01_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_01_bounds5 l).1) (fun l => (half_16_01_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_01_total1, half_16_01_total2, half_16_01_total3, half_16_01_total4, half_16_01_total5, half_16_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_01) (half_12_01)
    (by simpa only [half_16_01_φ6, show (2:ℝ)*32=64 by norm_num] using half_16_01_hx6)
  exact h.weaken (by norm_num [half_16_01_total1, half_16_01_total2, half_16_01_total3, half_16_01_total4, half_16_01_total5, half_16_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_01_hx4 : SourcePowerBound
    (powerBoxCross 9 12 16 half_16_01_φ4) (116409123407/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (381325883/5000000000 : ℝ)) half_16_01_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_01_bounds4 l).1) (fun l => (half_16_01_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_01_total1, half_16_01_total2, half_16_01_total3, half_16_01_total4, half_16_01_total5, half_16_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_01) (half_13_01)
    (by simpa only [half_16_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_01_hx5)
  exact h.weaken (by norm_num [half_16_01_total1, half_16_01_total2, half_16_01_total3, half_16_01_total4, half_16_01_total5, half_16_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_01_hx3 : SourcePowerBound
    (powerBoxCross 9 13 8 half_16_01_φ3) (70214729897/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (871602019/10000000000 : ℝ)) half_16_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_01_bounds3 l).1) (fun l => (half_16_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_01_total1, half_16_01_total2, half_16_01_total3, half_16_01_total4, half_16_01_total5, half_16_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_01) (half_14_01)
    (by simpa only [half_16_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_01_hx4)
  exact h.weaken (by norm_num [half_16_01_total1, half_16_01_total2, half_16_01_total3, half_16_01_total4, half_16_01_total5, half_16_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_01_hx2 : SourcePowerBound
    (powerBoxCross 9 14 4 half_16_01_φ2) (170436885049/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (970829819/10000000000 : ℝ)) half_16_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_01_bounds2 l).1) (fun l => (half_16_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_01_total1, half_16_01_total2, half_16_01_total3, half_16_01_total4, half_16_01_total5, half_16_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_01) (half_15_01)
    (by simpa only [half_16_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_01_hx3)
  exact h.weaken (by norm_num [half_16_01_total1, half_16_01_total2, half_16_01_total3, half_16_01_total4, half_16_01_total5, half_16_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_01_hx1 : SourcePowerBound
    (powerBoxCross 9 15 2 half_16_01_φ1) (205336058789/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (996342627/10000000000 : ℝ)) half_16_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_01_bounds1 l).1) (fun l => (half_16_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_01_total1, half_16_01_total2, half_16_01_total3, half_16_01_total4, half_16_01_total5, half_16_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_01) (chord_25)
    (by simpa only [half_16_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_01_hx2)
  exact h.weaken (by norm_num [half_16_01_total1, half_16_01_total2, half_16_01_total3, half_16_01_total4, half_16_01_total5, half_16_01_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_16_01 : AdmissibleExponent 9 32 (236076389331/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 14) (ψ := (530005699/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_15_01)
    (by simpa only [half_16_01_φ1] using half_16_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_01_total1, half_16_01_total2, half_16_01_total3, half_16_01_total4, half_16_01_total5, half_16_01_total6, parameterExponent, curveLoss, dyadicExponent])

theorem chord_31 : AdmissibleExponent 9 34 (511671920091/20000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 34) (t := (5/6 : ℝ))
    (half_16_01) (half_22_00)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_17_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (2092933/19531250 : ℝ)

private theorem half_17_01_total1 : total half_17_01_φ1=(2092933/19531250 : ℝ) := by
  norm_num [half_17_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_17_01_bounds1 : ∀ l,0≤half_17_01_φ1 l ∧ half_17_01_φ1 l≤1 ∧
    0≤shiftExponents 9 half_17_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (2092933/19531250 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_17_01_φ2 : Fin 2 → ℝ := Fin.snoc half_17_01_φ1 (1015926269/10000000000 : ℝ)

private theorem half_17_01_total2 : total half_17_01_φ2=(417501593/2000000000 : ℝ) := by
  change total (Fin.snoc half_17_01_φ1 (1015926269/10000000000 : ℝ))=(417501593/2000000000 : ℝ)
  rw [alternate_total_snoc,half_17_01_total1]
  norm_num

private theorem half_17_01_bounds2 : ∀ l,0≤half_17_01_φ2 l ∧ half_17_01_φ2 l≤1 ∧
    0≤shiftExponents 9 half_17_01_φ2 l :=
  alternate_bounds_snoc half_17_01_φ1 (1015926269/10000000000 : ℝ) half_17_01_bounds1 (by norm_num)

private def half_17_01_φ3 : Fin 3 → ℝ := Fin.snoc half_17_01_φ2 (7727043/78125000 : ℝ)

private theorem half_17_01_total3 : total half_17_01_φ3=(3076569469/10000000000 : ℝ) := by
  change total (Fin.snoc half_17_01_φ2 (7727043/78125000 : ℝ))=(3076569469/10000000000 : ℝ)
  rw [alternate_total_snoc,half_17_01_total2]
  norm_num

private theorem half_17_01_bounds3 : ∀ l,0≤half_17_01_φ3 l ∧ half_17_01_φ3 l≤1 ∧
    0≤shiftExponents 9 half_17_01_φ3 l :=
  alternate_bounds_snoc half_17_01_φ2 (7727043/78125000 : ℝ) half_17_01_bounds2 (by norm_num)

private def half_17_01_φ4 : Fin 4 → ℝ := Fin.snoc half_17_01_φ3 (54089301/625000000 : ℝ)

private theorem half_17_01_total4 : total half_17_01_φ4=(788399657/2000000000 : ℝ) := by
  change total (Fin.snoc half_17_01_φ3 (54089301/625000000 : ℝ))=(788399657/2000000000 : ℝ)
  rw [alternate_total_snoc,half_17_01_total3]
  norm_num

private theorem half_17_01_bounds4 : ∀ l,0≤half_17_01_φ4 l ∧ half_17_01_φ4 l≤1 ∧
    0≤shiftExponents 9 half_17_01_φ4 l :=
  alternate_bounds_snoc half_17_01_φ3 (54089301/625000000 : ℝ) half_17_01_bounds3 (by norm_num)

private def half_17_01_φ5 : Fin 5 → ℝ := Fin.snoc half_17_01_φ4 (378625107/5000000000 : ℝ)

private theorem half_17_01_total5 : total half_17_01_φ5=(4699248499/10000000000 : ℝ) := by
  change total (Fin.snoc half_17_01_φ4 (378625107/5000000000 : ℝ))=(4699248499/10000000000 : ℝ)
  rw [alternate_total_snoc,half_17_01_total4]
  norm_num

private theorem half_17_01_bounds5 : ∀ l,0≤half_17_01_φ5 l ∧ half_17_01_φ5 l≤1 ∧
    0≤shiftExponents 9 half_17_01_φ5 l :=
  alternate_bounds_snoc half_17_01_φ4 (378625107/5000000000 : ℝ) half_17_01_bounds4 (by norm_num)

private def half_17_01_φ6 : Fin 6 → ℝ := Fin.snoc half_17_01_φ5 (662593937/10000000000 : ℝ)

private theorem half_17_01_total6 : total half_17_01_φ6=(1340460609/2500000000 : ℝ) := by
  change total (Fin.snoc half_17_01_φ5 (662593937/10000000000 : ℝ))=(1340460609/2500000000 : ℝ)
  rw [alternate_total_snoc,half_17_01_total5]
  norm_num

private theorem half_17_01_bounds6 : ∀ l,0≤half_17_01_φ6 l ∧ half_17_01_φ6 l≤1 ∧
    0≤shiftExponents 9 half_17_01_φ6 l :=
  alternate_bounds_snoc half_17_01_φ5 (662593937/10000000000 : ℝ) half_17_01_bounds5 (by norm_num)

private theorem half_17_01_prefix : PrefixCondition 9 half_17_01_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_17_01_φ1, half_17_01_φ2, half_17_01_φ3, half_17_01_φ4, half_17_01_φ5, half_17_01_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_17_01_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_17_01_φ6) (2228618173/312500000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_17_01_φ6
    (fun i => (half_17_01_bounds6 i).1) (fun i => (half_17_01_bounds6 i).2.1)
    (fun i => (half_17_01_bounds6 i).2.2) half_17_01_prefix
  convert h using 1 <;> norm_num [half_17_01_total1, half_17_01_total2, half_17_01_total3, half_17_01_total4, half_17_01_total5, half_17_01_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_17_01_hx6 : SourcePowerBound
    (powerBoxCross 9 11 64 half_17_01_φ6) (9127692803/1000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 11) (r := 2) (v := 14) (w := 15) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_17_01_φ6 (by norm_num [half_17_01_total1, half_17_01_total2, half_17_01_total3, half_17_01_total4, half_17_01_total5, half_17_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_17_01_total1, half_17_01_total2, half_17_01_total3, half_17_01_total4, half_17_01_total5, half_17_01_total6, parameterExponent, curveLoss, dyadicExponent]) half_17_01_hF2
    (half_14_01) (half_15_01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_01_total1, half_17_01_total2, half_17_01_total3, half_17_01_total4, half_17_01_total5, half_17_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_01_hx5 : SourcePowerBound
    (powerBoxCross 9 12 32 half_17_01_φ5) (106657043337/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 12) (u := 10) (t := 13)
    (D := 32) (ψ := (662593937/10000000000 : ℝ)) half_17_01_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_01_bounds5 l).1) (fun l => (half_17_01_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_01_total1, half_17_01_total2, half_17_01_total3, half_17_01_total4, half_17_01_total5, half_17_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_01) (half_13_01)
    (by simpa only [half_17_01_φ6, show (2:ℝ)*32=64 by norm_num] using half_17_01_hx6)
  exact h.weaken (by norm_num [half_17_01_total1, half_17_01_total2, half_17_01_total3, half_17_01_total4, half_17_01_total5, half_17_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_01_hx4 : SourcePowerBound
    (powerBoxCross 9 13 16 half_17_01_φ4) (63242902949/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (378625107/5000000000 : ℝ)) half_17_01_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_01_bounds4 l).1) (fun l => (half_17_01_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_01_total1, half_17_01_total2, half_17_01_total3, half_17_01_total4, half_17_01_total5, half_17_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_01) (half_14_01)
    (by simpa only [half_17_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_01_hx5)
  exact h.weaken (by norm_num [half_17_01_total1, half_17_01_total2, half_17_01_total3, half_17_01_total4, half_17_01_total5, half_17_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_01_hx3 : SourcePowerBound
    (powerBoxCross 9 14 8 half_17_01_φ3) (151981466973/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (54089301/625000000 : ℝ)) half_17_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_01_bounds3 l).1) (fun l => (half_17_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_01_total1, half_17_01_total2, half_17_01_total3, half_17_01_total4, half_17_01_total5, half_17_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_01) (half_15_01)
    (by simpa only [half_17_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_01_hx4)
  exact h.weaken (by norm_num [half_17_01_total1, half_17_01_total2, half_17_01_total3, half_17_01_total4, half_17_01_total5, half_17_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_01_hx2 : SourcePowerBound
    (powerBoxCross 9 15 4 half_17_01_φ2) (184390659443/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (7727043/78125000 : ℝ)) half_17_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_01_bounds2 l).1) (fun l => (half_17_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_01_total1, half_17_01_total2, half_17_01_total3, half_17_01_total4, half_17_01_total5, half_17_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_01) (half_16_01)
    (by simpa only [half_17_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_01_hx3)
  exact h.weaken (by norm_num [half_17_01_total1, half_17_01_total2, half_17_01_total3, half_17_01_total4, half_17_01_total5, half_17_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_01_hx1 : SourcePowerBound
    (powerBoxCross 9 16 2 half_17_01_φ1) (221850457263/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (1015926269/10000000000 : ℝ)) half_17_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_01_bounds1 l).1) (fun l => (half_17_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_01_total1, half_17_01_total2, half_17_01_total3, half_17_01_total4, half_17_01_total5, half_17_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_01) (chord_31)
    (by simpa only [half_17_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_01_hx2)
  exact h.weaken (by norm_num [half_17_01_total1, half_17_01_total2, half_17_01_total3, half_17_01_total4, half_17_01_total5, half_17_01_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_17_01 : AdmissibleExponent 9 34 (255069489839/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 15) (ψ := (2092933/19531250 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_16_01)
    (by simpa only [half_17_01_φ1] using half_17_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_01_total1, half_17_01_total2, half_17_01_total3, half_17_01_total4, half_17_01_total5, half_17_01_total6, parameterExponent, curveLoss, dyadicExponent])

theorem chord_36 : AdmissibleExponent 9 36 (687455886487/25000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 36) (t := (4/5 : ℝ))
    (half_17_01) (half_22_00)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_18_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (541498109/5000000000 : ℝ)

private theorem half_18_01_total1 : total half_18_01_φ1=(541498109/5000000000 : ℝ) := by
  norm_num [half_18_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_18_01_bounds1 : ∀ l,0≤half_18_01_φ1 l ∧ half_18_01_φ1 l≤1 ∧
    0≤shiftExponents 9 half_18_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (541498109/5000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_18_01_φ2 : Fin 2 → ℝ := Fin.snoc half_18_01_φ1 (1033532487/10000000000 : ℝ)

private theorem half_18_01_total2 : total half_18_01_φ2=(423305741/2000000000 : ℝ) := by
  change total (Fin.snoc half_18_01_φ1 (1033532487/10000000000 : ℝ))=(423305741/2000000000 : ℝ)
  rw [alternate_total_snoc,half_18_01_total1]
  norm_num

private theorem half_18_01_bounds2 : ∀ l,0≤half_18_01_φ2 l ∧ half_18_01_φ2 l≤1 ∧
    0≤shiftExponents 9 half_18_01_φ2 l :=
  alternate_bounds_snoc half_18_01_φ1 (1033532487/10000000000 : ℝ) half_18_01_bounds1 (by norm_num)

private def half_18_01_φ3 : Fin 3 → ℝ := Fin.snoc half_18_01_φ2 (985433911/10000000000 : ℝ)

private theorem half_18_01_total3 : total half_18_01_φ3=(387745327/1250000000 : ℝ) := by
  change total (Fin.snoc half_18_01_φ2 (985433911/10000000000 : ℝ))=(387745327/1250000000 : ℝ)
  rw [alternate_total_snoc,half_18_01_total2]
  norm_num

private theorem half_18_01_bounds3 : ∀ l,0≤half_18_01_φ3 l ∧ half_18_01_φ3 l≤1 ∧
    0≤shiftExponents 9 half_18_01_φ3 l :=
  alternate_bounds_snoc half_18_01_φ2 (985433911/10000000000 : ℝ) half_18_01_bounds2 (by norm_num)

private def half_18_01_φ4 : Fin 4 → ℝ := Fin.snoc half_18_01_φ3 (53890917/625000000 : ℝ)

private theorem half_18_01_total4 : total half_18_01_φ4=(495527161/1250000000 : ℝ) := by
  change total (Fin.snoc half_18_01_φ3 (53890917/625000000 : ℝ))=(495527161/1250000000 : ℝ)
  rw [alternate_total_snoc,half_18_01_total3]
  norm_num

private theorem half_18_01_bounds4 : ∀ l,0≤half_18_01_φ4 l ∧ half_18_01_φ4 l≤1 ∧
    0≤shiftExponents 9 half_18_01_φ4 l :=
  alternate_bounds_snoc half_18_01_φ3 (53890917/625000000 : ℝ) half_18_01_bounds3 (by norm_num)

private def half_18_01_φ5 : Fin 5 → ℝ := Fin.snoc half_18_01_φ4 (377236419/5000000000 : ℝ)

private theorem half_18_01_total5 : total half_18_01_φ5=(2359345063/5000000000 : ℝ) := by
  change total (Fin.snoc half_18_01_φ4 (377236419/5000000000 : ℝ))=(2359345063/5000000000 : ℝ)
  rw [alternate_total_snoc,half_18_01_total4]
  norm_num

private theorem half_18_01_bounds5 : ∀ l,0≤half_18_01_φ5 l ∧ half_18_01_φ5 l≤1 ∧
    0≤shiftExponents 9 half_18_01_φ5 l :=
  alternate_bounds_snoc half_18_01_φ4 (377236419/5000000000 : ℝ) half_18_01_bounds4 (by norm_num)

private def half_18_01_φ6 : Fin 6 → ℝ := Fin.snoc half_18_01_φ5 (660163733/10000000000 : ℝ)

private theorem half_18_01_total6 : total half_18_01_φ6=(5378853859/10000000000 : ℝ) := by
  change total (Fin.snoc half_18_01_φ5 (660163733/10000000000 : ℝ))=(5378853859/10000000000 : ℝ)
  rw [alternate_total_snoc,half_18_01_total5]
  norm_num

private theorem half_18_01_bounds6 : ∀ l,0≤half_18_01_φ6 l ∧ half_18_01_φ6 l≤1 ∧
    0≤shiftExponents 9 half_18_01_φ6 l :=
  alternate_bounds_snoc half_18_01_φ5 (660163733/10000000000 : ℝ) half_18_01_bounds5 (by norm_num)

private theorem half_18_01_prefix : PrefixCondition 9 half_18_01_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_18_01_φ1, half_18_01_φ2, half_18_01_φ3, half_18_01_φ4, half_18_01_φ5, half_18_01_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_18_01_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_18_01_φ6) (8863438423/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_18_01_φ6
    (fun i => (half_18_01_bounds6 i).1) (fun i => (half_18_01_bounds6 i).2.1)
    (fun i => (half_18_01_bounds6 i).2.2) half_18_01_prefix
  convert h using 1 <;> norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_18_01_hx6 : SourcePowerBound
    (powerBoxCross 9 12 64 half_18_01_φ6) (24886909753/2500000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 12) (r := 2) (v := 0) (w := 16) (D := 64)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_18_01_φ6 (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, parameterExponent, curveLoss, dyadicExponent]) half_18_01_hF2
    (admissibleExponent_zero 9) (half_16_01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_01_hx5 : SourcePowerBound
    (powerBoxCross 9 13 32 half_18_01_φ5) (115987478419/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 13) (u := 11) (t := 14)
    (D := 32) (ψ := (660163733/10000000000 : ℝ)) half_18_01_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_01_bounds5 l).1) (fun l => (half_18_01_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_01) (half_14_01)
    (by simpa only [half_18_01_φ6, show (2:ℝ)*32=64 by norm_num] using half_18_01_hx6)
  exact h.weaken (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_01_hx4 : SourcePowerBound
    (powerBoxCross 9 14 16 half_18_01_φ4) (17143745939/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 14) (u := 12) (t := 15)
    (D := 16) (ψ := (377236419/5000000000 : ℝ)) half_18_01_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_01_bounds4 l).1) (fun l => (half_18_01_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_01) (half_15_01)
    (by simpa only [half_18_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_18_01_hx5)
  exact h.weaken (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_01_hx3 : SourcePowerBound
    (powerBoxCross 9 15 8 half_18_01_φ3) (164230759319/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 15) (u := 13) (t := 16)
    (D := 8) (ψ := (53890917/625000000 : ℝ)) half_18_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_01_bounds3 l).1) (fun l => (half_18_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_01) (half_16_01)
    (by simpa only [half_18_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_18_01_hx4)
  exact h.weaken (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_01_hx2 : SourcePowerBound
    (powerBoxCross 9 16 4 half_18_01_φ2) (99239853309/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 16) (u := 14) (t := 17)
    (D := 4) (ψ := (985433911/10000000000 : ℝ)) half_18_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_01_bounds2 l).1) (fun l => (half_18_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_01) (half_17_01)
    (by simpa only [half_18_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_18_01_hx3)
  exact h.weaken (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_01_hx1 : SourcePowerBound
    (powerBoxCross 9 17 2 half_18_01_φ1) (238528556781/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 17) (u := 15) (t := 18)
    (D := 2) (ψ := (1033532487/10000000000 : ℝ)) half_18_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_01_bounds1 l).1) (fun l => (half_18_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_01) (chord_36)
    (by simpa only [half_18_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_18_01_hx2)
  exact h.weaken (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_18_01 : AdmissibleExponent 9 36 (10970697279/400000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 16) (ψ := (541498109/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_17_01)
    (by simpa only [half_18_01_φ1] using half_18_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_18_01_total1, half_18_01_total2, half_18_01_total3, half_18_01_total4, half_18_01_total5, half_18_01_total6, parameterExponent, curveLoss, dyadicExponent])

theorem chord_40 : AdmissibleExponent 9 38 (1177436109543/40000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 38) (t := (3/4 : ℝ))
    (half_18_01) (half_22_00)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_19_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1094554251/10000000000 : ℝ)

private theorem half_19_01_total1 : total half_19_01_φ1=(1094554251/10000000000 : ℝ) := by
  norm_num [half_19_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_19_01_bounds1 : ∀ l,0≤half_19_01_φ1 l ∧ half_19_01_φ1 l≤1 ∧
    0≤shiftExponents 9 half_19_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (1094554251/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_19_01_φ2 : Fin 2 → ℝ := Fin.snoc half_19_01_φ1 (209727657/2000000000 : ℝ)

private theorem half_19_01_total2 : total half_19_01_φ2=(267899067/1250000000 : ℝ) := by
  change total (Fin.snoc half_19_01_φ1 (209727657/2000000000 : ℝ))=(267899067/1250000000 : ℝ)
  rw [alternate_total_snoc,half_19_01_total1]
  norm_num

private theorem half_19_01_bounds2 : ∀ l,0≤half_19_01_φ2 l ∧ half_19_01_φ2 l≤1 ∧
    0≤shiftExponents 9 half_19_01_φ2 l :=
  alternate_bounds_snoc half_19_01_φ1 (209727657/2000000000 : ℝ) half_19_01_bounds1 (by norm_num)

private def half_19_01_φ3 : Fin 3 → ℝ := Fin.snoc half_19_01_φ2 (245525233/2500000000 : ℝ)

private theorem half_19_01_total3 : total half_19_01_φ3=(781323367/2500000000 : ℝ) := by
  change total (Fin.snoc half_19_01_φ2 (245525233/2500000000 : ℝ))=(781323367/2500000000 : ℝ)
  rw [alternate_total_snoc,half_19_01_total2]
  norm_num

private theorem half_19_01_bounds3 : ∀ l,0≤half_19_01_φ3 l ∧ half_19_01_φ3 l≤1 ∧
    0≤shiftExponents 9 half_19_01_φ3 l :=
  alternate_bounds_snoc half_19_01_φ2 (245525233/2500000000 : ℝ) half_19_01_bounds2 (by norm_num)

private def half_19_01_φ4 : Fin 4 → ℝ := Fin.snoc half_19_01_φ3 (214834579/2500000000 : ℝ)

private theorem half_19_01_total4 : total half_19_01_φ4=(498078973/1250000000 : ℝ) := by
  change total (Fin.snoc half_19_01_φ3 (214834579/2500000000 : ℝ))=(498078973/1250000000 : ℝ)
  rw [alternate_total_snoc,half_19_01_total3]
  norm_num

private theorem half_19_01_bounds4 : ∀ l,0≤half_19_01_φ4 l ∧ half_19_01_φ4 l≤1 ∧
    0≤shiftExponents 9 half_19_01_φ4 l :=
  alternate_bounds_snoc half_19_01_φ3 (214834579/2500000000 : ℝ) half_19_01_bounds3 (by norm_num)

private def half_19_01_φ5 : Fin 5 → ℝ := Fin.snoc half_19_01_φ4 (375960513/5000000000 : ℝ)

private theorem half_19_01_total5 : total half_19_01_φ5=(473655281/1000000000 : ℝ) := by
  change total (Fin.snoc half_19_01_φ4 (375960513/5000000000 : ℝ))=(473655281/1000000000 : ℝ)
  rw [alternate_total_snoc,half_19_01_total4]
  norm_num

private theorem half_19_01_bounds5 : ∀ l,0≤half_19_01_φ5 l ∧ half_19_01_φ5 l≤1 ∧
    0≤shiftExponents 9 half_19_01_φ5 l :=
  alternate_bounds_snoc half_19_01_φ4 (375960513/5000000000 : ℝ) half_19_01_bounds4 (by norm_num)

private def half_19_01_φ6 : Fin 6 → ℝ := Fin.snoc half_19_01_φ5 (328965449/5000000000 : ℝ)

private theorem half_19_01_total6 : total half_19_01_φ6=(1348620927/2500000000 : ℝ) := by
  change total (Fin.snoc half_19_01_φ5 (328965449/5000000000 : ℝ))=(1348620927/2500000000 : ℝ)
  rw [alternate_total_snoc,half_19_01_total5]
  norm_num

private theorem half_19_01_bounds6 : ∀ l,0≤half_19_01_φ6 l ∧ half_19_01_φ6 l≤1 ∧
    0≤shiftExponents 9 half_19_01_φ6 l :=
  alternate_bounds_snoc half_19_01_φ5 (328965449/5000000000 : ℝ) half_19_01_bounds5 (by norm_num)

private theorem half_19_01_prefix : PrefixCondition 9 half_19_01_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_19_01_φ1, half_19_01_φ2, half_19_01_φ3, half_19_01_φ4, half_19_01_φ5, half_19_01_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_19_01_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_19_01_φ6) (2204137219/312500000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_19_01_φ6
    (fun i => (half_19_01_bounds6 i).1) (fun i => (half_19_01_bounds6 i).2.1)
    (fun i => (half_19_01_bounds6 i).2.2) half_19_01_prefix
  convert h using 1 <;> norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_19_01_hx6 : SourcePowerBound
    (powerBoxCross 9 13 64 half_19_01_φ6) (107948010463/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 13) (r := 2) (v := 17) (w := 18) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_19_01_φ6 (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, parameterExponent, curveLoss, dyadicExponent]) half_19_01_hF2
    (half_17_01) (half_18_01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_01_hx5 : SourcePowerBound
    (powerBoxCross 9 14 32 half_19_01_φ5) (125442255687/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 14) (u := 12) (t := 15)
    (D := 32) (ψ := (328965449/5000000000 : ℝ)) half_19_01_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_01_bounds5 l).1) (fun l => (half_19_01_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_01) (half_15_01)
    (by simpa only [half_19_01_φ6, show (2:ℝ)*32=64 by norm_num] using half_19_01_hx6)
  exact h.weaken (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_01_hx4 : SourcePowerBound
    (powerBoxCross 9 15 16 half_19_01_φ4) (29587571001/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 15) (u := 13) (t := 16)
    (D := 16) (ψ := (375960513/5000000000 : ℝ)) half_19_01_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_01_bounds4 l).1) (fun l => (half_19_01_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_01) (half_16_01)
    (by simpa only [half_19_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_19_01_hx5)
  exact h.weaken (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_01_hx3 : SourcePowerBound
    (powerBoxCross 9 16 8 half_19_01_φ3) (176604553609/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 16) (u := 14) (t := 17)
    (D := 8) (ψ := (214834579/2500000000 : ℝ)) half_19_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_01_bounds3 l).1) (fun l => (half_19_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_01) (half_17_01)
    (by simpa only [half_19_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_19_01_hx4)
  exact h.weaken (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_01_hx2 : SourcePowerBound
    (powerBoxCross 9 17 4 half_19_01_φ2) (212695391441/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 17) (u := 15) (t := 18)
    (D := 4) (ψ := (245525233/2500000000 : ℝ)) half_19_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_01_bounds2 l).1) (fun l => (half_19_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_01) (half_18_01)
    (by simpa only [half_19_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_19_01_hx3)
  exact h.weaken (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_01_hx1 : SourcePowerBound
    (powerBoxCross 9 18 2 half_19_01_φ1) (2042735423/80000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 18) (u := 16) (t := 19)
    (D := 2) (ψ := (209727657/2000000000 : ℝ)) half_19_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_01_bounds1 l).1) (fun l => (half_19_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_01) (chord_40)
    (by simpa only [half_19_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_19_01_hx2)
  exact h.weaken (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_19_01 : AdmissibleExponent 9 38 (14682566333/500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 17) (ψ := (1094554251/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_18_01)
    (by simpa only [half_19_01_φ1] using half_19_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_19_01_total1, half_19_01_total2, half_19_01_total3, half_19_01_total4, half_19_01_total5, half_19_01_total6, parameterExponent, curveLoss, dyadicExponent])

theorem chord_43 : AdmissibleExponent 9 40 (470968233469/15000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 40) (t := (2/3 : ℝ))
    (half_19_01) (half_22_00)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_20_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1107715947/10000000000 : ℝ)

private theorem half_20_01_total1 : total half_20_01_φ1=(1107715947/10000000000 : ℝ) := by
  norm_num [half_20_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_20_01_bounds1 : ∀ l,0≤half_20_01_φ1 l ∧ half_20_01_φ1 l≤1 ∧
    0≤shiftExponents 9 half_20_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (1107715947/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_20_01_φ2 : Fin 2 → ℝ := Fin.snoc half_20_01_φ1 (530709069/5000000000 : ℝ)

private theorem half_20_01_total2 : total half_20_01_φ2=(433826817/2000000000 : ℝ) := by
  change total (Fin.snoc half_20_01_φ1 (530709069/5000000000 : ℝ))=(433826817/2000000000 : ℝ)
  rw [alternate_total_snoc,half_20_01_total1]
  norm_num

private theorem half_20_01_bounds2 : ∀ l,0≤half_20_01_φ2 l ∧ half_20_01_φ2 l≤1 ∧
    0≤shiftExponents 9 half_20_01_φ2 l :=
  alternate_bounds_snoc half_20_01_φ1 (530709069/5000000000 : ℝ) half_20_01_bounds1 (by norm_num)

private def half_20_01_φ3 : Fin 3 → ℝ := Fin.snoc half_20_01_φ2 (978858239/10000000000 : ℝ)

private theorem half_20_01_total3 : total half_20_01_φ3=(786998081/2500000000 : ℝ) := by
  change total (Fin.snoc half_20_01_φ2 (978858239/10000000000 : ℝ))=(786998081/2500000000 : ℝ)
  rw [alternate_total_snoc,half_20_01_total2]
  norm_num

private theorem half_20_01_bounds3 : ∀ l,0≤half_20_01_φ3 l ∧ half_20_01_φ3 l≤1 ∧
    0≤shiftExponents 9 half_20_01_φ3 l :=
  alternate_bounds_snoc half_20_01_φ2 (978858239/10000000000 : ℝ) half_20_01_bounds2 (by norm_num)

private def half_20_01_φ4 : Fin 4 → ℝ := Fin.snoc half_20_01_φ3 (856500959/10000000000 : ℝ)

private theorem half_20_01_total4 : total half_20_01_φ4=(4004493283/10000000000 : ℝ) := by
  change total (Fin.snoc half_20_01_φ3 (856500959/10000000000 : ℝ))=(4004493283/10000000000 : ℝ)
  rw [alternate_total_snoc,half_20_01_total3]
  norm_num

private theorem half_20_01_bounds4 : ∀ l,0≤half_20_01_φ4 l ∧ half_20_01_φ4 l≤1 ∧
    0≤shiftExponents 9 half_20_01_φ4 l :=
  alternate_bounds_snoc half_20_01_φ3 (856500959/10000000000 : ℝ) half_20_01_bounds3 (by norm_num)

private def half_20_01_φ5 : Fin 5 → ℝ := Fin.snoc half_20_01_φ4 (749438339/10000000000 : ℝ)

private theorem half_20_01_total5 : total half_20_01_φ5=(2376965811/5000000000 : ℝ) := by
  change total (Fin.snoc half_20_01_φ4 (749438339/10000000000 : ℝ))=(2376965811/5000000000 : ℝ)
  rw [alternate_total_snoc,half_20_01_total4]
  norm_num

private theorem half_20_01_bounds5 : ∀ l,0≤half_20_01_φ5 l ∧ half_20_01_φ5 l≤1 ∧
    0≤shiftExponents 9 half_20_01_φ5 l :=
  alternate_bounds_snoc half_20_01_φ4 (749438339/10000000000 : ℝ) half_20_01_bounds4 (by norm_num)

private def half_20_01_φ6 : Fin 6 → ℝ := Fin.snoc half_20_01_φ5 (327879273/5000000000 : ℝ)

private theorem half_20_01_total6 : total half_20_01_φ6=(676211271/1250000000 : ℝ) := by
  change total (Fin.snoc half_20_01_φ5 (327879273/5000000000 : ℝ))=(676211271/1250000000 : ℝ)
  rw [alternate_total_snoc,half_20_01_total5]
  norm_num

private theorem half_20_01_bounds6 : ∀ l,0≤half_20_01_φ6 l ∧ half_20_01_φ6 l≤1 ∧
    0≤shiftExponents 9 half_20_01_φ6 l :=
  alternate_bounds_snoc half_20_01_φ5 (327879273/5000000000 : ℝ) half_20_01_bounds5 (by norm_num)

private theorem half_20_01_prefix : PrefixCondition 9 half_20_01_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_20_01_φ1, half_20_01_φ2, half_20_01_φ3, half_20_01_φ4, half_20_01_φ5, half_20_01_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_20_01_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_20_01_φ6) (1096366187/156250000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_20_01_φ6
    (fun i => (half_20_01_bounds6 i).1) (fun i => (half_20_01_bounds6 i).2.1)
    (fun i => (half_20_01_bounds6 i).2.2) half_20_01_prefix
  convert h using 1 <;> norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_20_01_hx6 : SourcePowerBound
    (powerBoxCross 9 14 64 half_20_01_φ6) (11641369983/1000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 14) (r := 2) (v := 18) (w := 19) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_20_01_φ6 (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, parameterExponent, curveLoss, dyadicExponent]) half_20_01_hF2
    (half_18_01) (half_19_01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_01_hx5 : SourcePowerBound
    (powerBoxCross 9 15 32 half_20_01_φ5) (67483753921/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 15) (u := 13) (t := 16)
    (D := 32) (ψ := (327879273/5000000000 : ℝ)) half_20_01_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_01_bounds5 l).1) (fun l => (half_20_01_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_01) (half_16_01)
    (by simpa only [half_20_01_φ6, show (2:ℝ)*32=64 by norm_num] using half_20_01_hx6)
  exact h.weaken (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_01_hx4 : SourcePowerBound
    (powerBoxCross 9 16 16 half_20_01_φ4) (158796178687/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 16) (u := 14) (t := 17)
    (D := 16) (ψ := (749438339/10000000000 : ℝ)) half_20_01_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_01_bounds4 l).1) (fun l => (half_20_01_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_01) (half_17_01)
    (by simpa only [half_20_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_20_01_hx5)
  exact h.weaken (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_01_hx3 : SourcePowerBound
    (powerBoxCross 9 17 8 half_20_01_φ3) (189046012371/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 17) (u := 15) (t := 18)
    (D := 8) (ψ := (856500959/10000000000 : ℝ)) half_20_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_01_bounds3 l).1) (fun l => (half_20_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_01) (half_18_01)
    (by simpa only [half_20_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_20_01_hx4)
  exact h.weaken (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_01_hx2 : SourcePowerBound
    (powerBoxCross 9 18 4 half_20_01_φ2) (226974839031/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 18) (u := 16) (t := 19)
    (D := 4) (ψ := (978858239/10000000000 : ℝ)) half_20_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_01_bounds2 l).1) (fun l => (half_20_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_01) (half_19_01)
    (by simpa only [half_20_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_20_01_hx3)
  exact h.weaken (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_01_hx1 : SourcePowerBound
    (powerBoxCross 9 19 2 half_20_01_φ1) (435569307/16000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 19) (u := 17) (t := 20)
    (D := 2) (ψ := (530709069/5000000000 : ℝ)) half_20_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_01_bounds1 l).1) (fun l => (half_20_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_01) (chord_43)
    (by simpa only [half_20_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_20_01_hx2)
  exact h.weaken (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_20_01 : AdmissibleExponent 9 40 (156608153457/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 18) (ψ := (1107715947/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_19_01)
    (by simpa only [half_20_01_φ1] using half_20_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_20_01_total1, half_20_01_total2, half_20_01_total3, half_20_01_total4, half_20_01_total5, half_20_01_total6, parameterExponent, curveLoss, dyadicExponent])

theorem chord_45 : AdmissibleExponent 9 42 (166962530133/5000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 42) (t := (1/2 : ℝ))
    (half_20_01) (half_22_00)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_21_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1111111111/10000000000 : ℝ)

private theorem half_21_01_total1 : total half_21_01_φ1=(1111111111/10000000000 : ℝ) := by
  norm_num [half_21_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_21_01_bounds1 : ∀ l,0≤half_21_01_φ1 l ∧ half_21_01_φ1 l≤1 ∧
    0≤shiftExponents 9 half_21_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (1111111111/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_21_01_φ2 : Fin 2 → ℝ := Fin.snoc half_21_01_φ1 (214513373/2000000000 : ℝ)

private theorem half_21_01_total2 : total half_21_01_φ2=(272959747/1250000000 : ℝ) := by
  change total (Fin.snoc half_21_01_φ1 (214513373/2000000000 : ℝ))=(272959747/1250000000 : ℝ)
  rw [alternate_total_snoc,half_21_01_total1]
  norm_num

private theorem half_21_01_bounds2 : ∀ l,0≤half_21_01_φ2 l ∧ half_21_01_φ2 l≤1 ∧
    0≤shiftExponents 9 half_21_01_φ2 l :=
  alternate_bounds_snoc half_21_01_φ1 (214513373/2000000000 : ℝ) half_21_01_bounds1 (by norm_num)

private def half_21_01_φ3 : Fin 3 → ℝ := Fin.snoc half_21_01_φ2 (244260063/2500000000 : ℝ)

private theorem half_21_01_total3 : total half_21_01_φ3=(790179557/2500000000 : ℝ) := by
  change total (Fin.snoc half_21_01_φ2 (244260063/2500000000 : ℝ))=(790179557/2500000000 : ℝ)
  rw [alternate_total_snoc,half_21_01_total2]
  norm_num

private theorem half_21_01_bounds3 : ∀ l,0≤half_21_01_φ3 l ∧ half_21_01_φ3 l≤1 ∧
    0≤shiftExponents 9 half_21_01_φ3 l :=
  alternate_bounds_snoc half_21_01_φ2 (244260063/2500000000 : ℝ) half_21_01_bounds2 (by norm_num)

private def half_21_01_φ4 : Fin 4 → ℝ := Fin.snoc half_21_01_φ3 (854910221/10000000000 : ℝ)

private theorem half_21_01_total4 : total half_21_01_φ4=(4015628449/10000000000 : ℝ) := by
  change total (Fin.snoc half_21_01_φ3 (854910221/10000000000 : ℝ))=(4015628449/10000000000 : ℝ)
  rw [alternate_total_snoc,half_21_01_total3]
  norm_num

private theorem half_21_01_bounds4 : ∀ l,0≤half_21_01_φ4 l ∧ half_21_01_φ4 l≤1 ∧
    0≤shiftExponents 9 half_21_01_φ4 l :=
  alternate_bounds_snoc half_21_01_φ3 (854910221/10000000000 : ℝ) half_21_01_bounds3 (by norm_num)

private def half_21_01_φ5 : Fin 5 → ℝ := Fin.snoc half_21_01_φ4 (748046443/10000000000 : ℝ)

private theorem half_21_01_total5 : total half_21_01_φ5=(1190918723/2500000000 : ℝ) := by
  change total (Fin.snoc half_21_01_φ4 (748046443/10000000000 : ℝ))=(1190918723/2500000000 : ℝ)
  rw [alternate_total_snoc,half_21_01_total4]
  norm_num

private theorem half_21_01_bounds5 : ∀ l,0≤half_21_01_φ5 l ∧ half_21_01_φ5 l≤1 ∧
    0≤shiftExponents 9 half_21_01_φ5 l :=
  alternate_bounds_snoc half_21_01_φ4 (748046443/10000000000 : ℝ) half_21_01_bounds4 (by norm_num)

private def half_21_01_φ6 : Fin 6 → ℝ := Fin.snoc half_21_01_φ5 (327270319/5000000000 : ℝ)

private theorem half_21_01_total6 : total half_21_01_φ6=(541821553/1000000000 : ℝ) := by
  change total (Fin.snoc half_21_01_φ5 (327270319/5000000000 : ℝ))=(541821553/1000000000 : ℝ)
  rw [alternate_total_snoc,half_21_01_total5]
  norm_num

private theorem half_21_01_bounds6 : ∀ l,0≤half_21_01_φ6 l ∧ half_21_01_φ6 l≤1 ∧
    0≤shiftExponents 9 half_21_01_φ6 l :=
  alternate_bounds_snoc half_21_01_φ5 (327270319/5000000000 : ℝ) half_21_01_bounds5 (by norm_num)

private theorem half_21_01_prefix : PrefixCondition 9 half_21_01_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_21_01_φ1, half_21_01_φ2, half_21_01_φ3, half_21_01_φ4, half_21_01_φ5, half_21_01_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_21_01_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_21_01_φ6) (874535341/125000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_21_01_φ6
    (fun i => (half_21_01_bounds6 i).1) (fun i => (half_21_01_bounds6 i).2.1)
    (fun i => (half_21_01_bounds6 i).2.2) half_21_01_prefix
  convert h using 1 <;> norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_21_01_hx6 : SourcePowerBound
    (powerBoxCross 9 15 64 half_21_01_φ6) (31280606907/2500000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 15) (r := 2) (v := 0) (w := 20) (D := 64)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_21_01_φ6 (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, parameterExponent, curveLoss, dyadicExponent]) half_21_01_hF2
    (admissibleExponent_zero 9) (half_20_01)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_01_hx5 : SourcePowerBound
    (powerBoxCross 9 16 32 half_21_01_φ5) (72389346097/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 16) (u := 14) (t := 17)
    (D := 32) (ψ := (327270319/5000000000 : ℝ)) half_21_01_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_01_bounds5 l).1) (fun l => (half_21_01_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_01) (half_17_01)
    (by simpa only [half_21_01_φ6, show (2:ℝ)*32=64 by norm_num] using half_21_01_hx6)
  exact h.weaken (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_01_hx4 : SourcePowerBound
    (powerBoxCross 9 17 16 half_21_01_φ4) (21248432879/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 17) (u := 15) (t := 18)
    (D := 16) (ψ := (748046443/10000000000 : ℝ)) half_21_01_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_01_bounds4 l).1) (fun l => (half_21_01_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_01) (half_18_01)
    (by simpa only [half_21_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_21_01_hx5)
  exact h.weaken (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_01_hx3 : SourcePowerBound
    (powerBoxCross 9 18 8 half_21_01_φ3) (100937542769/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 18) (u := 16) (t := 19)
    (D := 8) (ψ := (854910221/10000000000 : ℝ)) half_21_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_01_bounds3 l).1) (fun l => (half_21_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_01) (half_19_01)
    (by simpa only [half_21_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_21_01_hx4)
  exact h.weaken (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_01_hx2 : SourcePowerBound
    (powerBoxCross 9 19 4 half_21_01_φ2) (30213876397/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 19) (u := 17) (t := 20)
    (D := 4) (ψ := (244260063/2500000000 : ℝ)) half_21_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_01_bounds2 l).1) (fun l => (half_21_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_01) (half_20_01)
    (by simpa only [half_21_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_21_01_hx3)
  exact h.weaken (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_21_01_hx1 : SourcePowerBound
    (powerBoxCross 9 20 2 half_21_01_φ1) (57932937209/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 20) (u := 18) (t := 21)
    (D := 2) (ψ := (214513373/2000000000 : ℝ)) half_21_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_21_01_bounds1 l).1) (fun l => (half_21_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_19_01) (chord_45)
    (by simpa only [half_21_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_21_01_hx2)
  exact h.weaken (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_21_01 : AdmissibleExponent 9 42 (166499009687/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 19) (ψ := (1111111111/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_20_01)
    (by simpa only [half_21_01_φ1] using half_21_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_21_01_total1, half_21_01_total2, half_21_01_total3, half_21_01_total4, half_21_01_total5, half_21_01_total6, parameterExponent, curveLoss, dyadicExponent])

end Waring.SeedCompletionAlternate9Seeds
