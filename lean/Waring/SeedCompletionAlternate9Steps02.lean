import Waring.SeedCompletionAlternate9Steps01

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionAlternate9Seeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges SeedCompletionDivisorPowerScales
open PolicyCompletionSharpResidualSource

private def half_22_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1111111111/10000000000 : ℝ)

private theorem half_22_01_total1 : total half_22_01_φ1=(1111111111/10000000000 : ℝ) := by
  norm_num [half_22_01_φ1,total,emptyPhi,Fin.snoc]

private theorem half_22_01_bounds1 : ∀ l,0≤half_22_01_φ1 l ∧ half_22_01_φ1 l≤1 ∧
    0≤shiftExponents 9 half_22_01_φ1 l :=
  alternate_bounds_snoc emptyPhi (1111111111/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_22_01_φ2 : Fin 2 → ℝ := Fin.snoc half_22_01_φ1 (1085389197/10000000000 : ℝ)

private theorem half_22_01_total2 : total half_22_01_φ2=(549125077/2500000000 : ℝ) := by
  change total (Fin.snoc half_22_01_φ1 (1085389197/10000000000 : ℝ))=(549125077/2500000000 : ℝ)
  rw [alternate_total_snoc,half_22_01_total1]
  norm_num

private theorem half_22_01_bounds2 : ∀ l,0≤half_22_01_φ2 l ∧ half_22_01_φ2 l≤1 ∧
    0≤shiftExponents 9 half_22_01_φ2 l :=
  alternate_bounds_snoc half_22_01_φ1 (1085389197/10000000000 : ℝ) half_22_01_bounds1 (by norm_num)

private def half_22_01_φ3 : Fin 3 → ℝ := Fin.snoc half_22_01_φ2 (975437461/10000000000 : ℝ)

private theorem half_22_01_total3 : total half_22_01_φ3=(3171937769/10000000000 : ℝ) := by
  change total (Fin.snoc half_22_01_φ2 (975437461/10000000000 : ℝ))=(3171937769/10000000000 : ℝ)
  rw [alternate_total_snoc,half_22_01_total2]
  norm_num

private theorem half_22_01_bounds3 : ∀ l,0≤half_22_01_φ3 l ∧ half_22_01_φ3 l≤1 ∧
    0≤shiftExponents 9 half_22_01_φ3 l :=
  alternate_bounds_snoc half_22_01_φ2 (975437461/10000000000 : ℝ) half_22_01_bounds2 (by norm_num)

private def half_22_01_φ4 : Fin 4 → ℝ := Fin.snoc half_22_01_φ3 (426753889/5000000000 : ℝ)

private theorem half_22_01_total4 : total half_22_01_φ4=(4025445547/10000000000 : ℝ) := by
  change total (Fin.snoc half_22_01_φ3 (426753889/5000000000 : ℝ))=(4025445547/10000000000 : ℝ)
  rw [alternate_total_snoc,half_22_01_total3]
  norm_num

private theorem half_22_01_bounds4 : ∀ l,0≤half_22_01_φ4 l ∧ half_22_01_φ4 l≤1 ∧
    0≤shiftExponents 9 half_22_01_φ4 l :=
  alternate_bounds_snoc half_22_01_φ3 (426753889/5000000000 : ℝ) half_22_01_bounds3 (by norm_num)

private def half_22_01_φ5 : Fin 5 → ℝ := Fin.snoc half_22_01_φ4 (373409653/5000000000 : ℝ)

private theorem half_22_01_total5 : total half_22_01_φ5=(4772264853/10000000000 : ℝ) := by
  change total (Fin.snoc half_22_01_φ4 (373409653/5000000000 : ℝ))=(4772264853/10000000000 : ℝ)
  rw [alternate_total_snoc,half_22_01_total4]
  norm_num

private theorem half_22_01_bounds5 : ∀ l,0≤half_22_01_φ5 l ∧ half_22_01_φ5 l≤1 ∧
    0≤shiftExponents 9 half_22_01_φ5 l :=
  alternate_bounds_snoc half_22_01_φ4 (373409653/5000000000 : ℝ) half_22_01_bounds4 (by norm_num)

private def half_22_01_φ6 : Fin 6 → ℝ := Fin.snoc half_22_01_φ5 (653466893/10000000000 : ℝ)

private theorem half_22_01_total6 : total half_22_01_φ6=(2712865873/5000000000 : ℝ) := by
  change total (Fin.snoc half_22_01_φ5 (653466893/10000000000 : ℝ))=(2712865873/5000000000 : ℝ)
  rw [alternate_total_snoc,half_22_01_total5]
  norm_num

private theorem half_22_01_bounds6 : ∀ l,0≤half_22_01_φ6 l ∧ half_22_01_φ6 l≤1 ∧
    0≤shiftExponents 9 half_22_01_φ6 l :=
  alternate_bounds_snoc half_22_01_φ5 (653466893/10000000000 : ℝ) half_22_01_bounds5 (by norm_num)

private theorem half_22_01_prefix : PrefixCondition 9 half_22_01_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_22_01_φ1, half_22_01_φ2, half_22_01_φ3, half_22_01_φ4, half_22_01_φ5, half_22_01_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_22_01_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_22_01_φ6) (4361402381/625000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_22_01_φ6
    (fun i => (half_22_01_bounds6 i).1) (fun i => (half_22_01_bounds6 i).2.1)
    (fun i => (half_22_01_bounds6 i).2.2) half_22_01_prefix
  convert h using 1 <;> norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_22_01_hx6 : SourcePowerBound
    (powerBoxCross 9 16 64 half_22_01_φ6) (33540369461/2500000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 16) (r := 2) (v := 21) (w := 22) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_22_01_φ6 (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, parameterExponent, curveLoss, dyadicExponent]) half_22_01_hF2
    (half_21_01) (half_22_00)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_01_hx5 : SourcePowerBound
    (powerBoxCross 9 17 32 half_22_01_φ5) (154810291043/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 17) (u := 15) (t := 18)
    (D := 32) (ψ := (653466893/10000000000 : ℝ)) half_22_01_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_01_bounds5 l).1) (fun l => (half_22_01_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_01) (half_18_01)
    (by simpa only [half_22_01_φ6, show (2:ℝ)*32=64 by norm_num] using half_22_01_hx6)
  exact h.weaken (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_01_hx4 : SourcePowerBound
    (powerBoxCross 9 18 16 half_22_01_φ4) (181347673949/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 18) (u := 16) (t := 19)
    (D := 16) (ψ := (373409653/5000000000 : ℝ)) half_22_01_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_01_bounds4 l).1) (fun l => (half_22_01_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_01) (half_19_01)
    (by simpa only [half_22_01_φ5, show (2:ℝ)*16=32 by norm_num] using half_22_01_hx5)
  exact h.weaken (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_01_hx3 : SourcePowerBound
    (powerBoxCross 9 19 8 half_22_01_φ3) (214855493783/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 19) (u := 17) (t := 20)
    (D := 8) (ψ := (426753889/5000000000 : ℝ)) half_22_01_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_01_bounds3 l).1) (fun l => (half_22_01_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_01) (half_20_01)
    (by simpa only [half_22_01_φ4, show (2:ℝ)*8=16 by norm_num] using half_22_01_hx4)
  exact h.weaken (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_01_hx2 : SourcePowerBound
    (powerBoxCross 9 20 4 half_22_01_φ2) (25661483577/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 20) (u := 18) (t := 21)
    (D := 4) (ψ := (975437461/10000000000 : ℝ)) half_22_01_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_01_bounds2 l).1) (fun l => (half_22_01_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_19_01) (half_21_01)
    (by simpa only [half_22_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_22_01_hx3)
  exact h.weaken (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_22_01_hx1 : SourcePowerBound
    (powerBoxCross 9 21 2 half_22_01_φ1) (15382154553/500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 21) (u := 19) (t := 22)
    (D := 2) (ψ := (1085389197/10000000000 : ℝ)) half_22_01_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_22_01_bounds1 l).1) (fun l => (half_22_01_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_20_01) (half_22_00)
    (by simpa only [half_22_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_22_01_hx2)
  exact h.weaken (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_22_01 : AdmissibleExponent 9 44 (353198646611/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 20) (ψ := (1111111111/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_21_01)
    (by simpa only [half_22_01_φ1] using half_22_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_22_01_total1, half_22_01_total2, half_22_01_total3, half_22_01_total4, half_22_01_total5, half_22_01_total6, parameterExponent, curveLoss, dyadicExponent])

private def half_10_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (454083127/5000000000 : ℝ)

private theorem half_10_02_total1 : total half_10_02_φ1=(454083127/5000000000 : ℝ) := by
  norm_num [half_10_02_φ1,total,emptyPhi,Fin.snoc]

private theorem half_10_02_bounds1 : ∀ l,0≤half_10_02_φ1 l ∧ half_10_02_φ1 l≤1 ∧
    0≤shiftExponents 9 half_10_02_φ1 l :=
  alternate_bounds_snoc emptyPhi (454083127/5000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_10_02_φ2 : Fin 2 → ℝ := Fin.snoc half_10_02_φ1 (822002867/10000000000 : ℝ)

private theorem half_10_02_total2 : total half_10_02_φ2=(1730169121/10000000000 : ℝ) := by
  change total (Fin.snoc half_10_02_φ1 (822002867/10000000000 : ℝ))=(1730169121/10000000000 : ℝ)
  rw [alternate_total_snoc,half_10_02_total1]
  norm_num

private theorem half_10_02_bounds2 : ∀ l,0≤half_10_02_φ2 l ∧ half_10_02_φ2 l≤1 ∧
    0≤shiftExponents 9 half_10_02_φ2 l :=
  alternate_bounds_snoc half_10_02_φ1 (822002867/10000000000 : ℝ) half_10_02_bounds1 (by norm_num)

private def half_10_02_φ3 : Fin 3 → ℝ := Fin.snoc half_10_02_φ2 (359358739/5000000000 : ℝ)

private theorem half_10_02_total3 : total half_10_02_φ3=(2448886599/10000000000 : ℝ) := by
  change total (Fin.snoc half_10_02_φ2 (359358739/5000000000 : ℝ))=(2448886599/10000000000 : ℝ)
  rw [alternate_total_snoc,half_10_02_total2]
  norm_num

private theorem half_10_02_bounds3 : ∀ l,0≤half_10_02_φ3 l ∧ half_10_02_φ3 l≤1 ∧
    0≤shiftExponents 9 half_10_02_φ3 l :=
  alternate_bounds_snoc half_10_02_φ2 (359358739/5000000000 : ℝ) half_10_02_bounds2 (by norm_num)

private def half_10_02_φ4 : Fin 4 → ℝ := Fin.snoc half_10_02_φ3 (228162393/5000000000 : ℝ)

private theorem half_10_02_total4 : total half_10_02_φ4=(581042277/2000000000 : ℝ) := by
  change total (Fin.snoc half_10_02_φ3 (228162393/5000000000 : ℝ))=(581042277/2000000000 : ℝ)
  rw [alternate_total_snoc,half_10_02_total3]
  norm_num

private theorem half_10_02_bounds4 : ∀ l,0≤half_10_02_φ4 l ∧ half_10_02_φ4 l≤1 ∧
    0≤shiftExponents 9 half_10_02_φ4 l :=
  alternate_bounds_snoc half_10_02_φ3 (228162393/5000000000 : ℝ) half_10_02_bounds3 (by norm_num)

private theorem half_10_02_prefix : PrefixCondition 9 half_10_02_φ4 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_10_02_φ1, half_10_02_φ2, half_10_02_φ3, half_10_02_φ4, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_10_02_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 16 half_10_02_φ4) (1756873169/250000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 9) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_02_φ4
    (fun i => (half_10_02_bounds4 i).1) (fun i => (half_10_02_bounds4 i).2.1)
    (fun i => (half_10_02_bounds4 i).2.2) half_10_02_prefix
  convert h using 1 <;> norm_num [half_10_02_total1, half_10_02_total2, half_10_02_total3, half_10_02_total4, parameterExponent, curveLoss, dyadicExponent]

private theorem half_10_02_hx4 : SourcePowerBound
    (powerBoxCross 9 6 16 half_10_02_φ4) (4292006603/625000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 6) (r := 2) (v := 0) (w := 8) (D := 16)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_10_02_φ4 (by norm_num [half_10_02_total1, half_10_02_total2, half_10_02_total3, half_10_02_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_10_02_total1, half_10_02_total2, half_10_02_total3, half_10_02_total4, parameterExponent, curveLoss, dyadicExponent]) half_10_02_hF2
    (admissibleExponent_zero 9) (SeedCompletionHigher9SimpleSeeds.degree9_half_8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_02_total1, half_10_02_total2, half_10_02_total3, half_10_02_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_10_02_hx3 : SourcePowerBound
    (powerBoxCross 9 7 8 half_10_02_φ3) (7831046369/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 7) (u := 5) (t := 8)
    (D := 8) (ψ := (228162393/5000000000 : ℝ)) half_10_02_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_10_02_bounds3 l).1) (fun l => (half_10_02_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_10_02_total1, half_10_02_total2, half_10_02_total3, half_10_02_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_6) (SeedCompletionHigher9SimpleSeeds.degree9_half_8)
    (by simpa only [half_10_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_10_02_hx4)
  exact h.weaken (by norm_num [half_10_02_total1, half_10_02_total2, half_10_02_total3, half_10_02_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_10_02_hx2 : SourcePowerBound
    (powerBoxCross 9 8 4 half_10_02_φ2) (92979524911/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (359358739/5000000000 : ℝ)) half_10_02_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_10_02_bounds2 l).1) (fun l => (half_10_02_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_10_02_total1, half_10_02_total2, half_10_02_total3, half_10_02_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_7) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_10_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_02_hx3)
  exact h.weaken (by norm_num [half_10_02_total1, half_10_02_total2, half_10_02_total3, half_10_02_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_10_02_hx1 : SourcePowerBound
    (powerBoxCross 9 9 2 half_10_02_φ1) (11221394721/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (822002867/10000000000 : ℝ)) half_10_02_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_10_02_bounds1 l).1) (fun l => (half_10_02_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_10_02_total1, half_10_02_total2, half_10_02_total3, half_10_02_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_01)
    (by simpa only [half_10_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_02_hx2)
  exact h.weaken (by norm_num [half_10_02_total1, half_10_02_total2, half_10_02_total3, half_10_02_total4, parameterExponent, curveLoss, dyadicExponent])

theorem half_10_02 : AdmissibleExponent 9 20 (15956596691/1250000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 8) (ψ := (454083127/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_10_02_φ1] using half_10_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_02_total1, half_10_02_total2, half_10_02_total3, half_10_02_total4, parameterExponent, curveLoss, dyadicExponent])

private def half_11_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (951961669/10000000000 : ℝ)

private theorem half_11_02_total1 : total half_11_02_φ1=(951961669/10000000000 : ℝ) := by
  norm_num [half_11_02_φ1,total,emptyPhi,Fin.snoc]

private theorem half_11_02_bounds1 : ∀ l,0≤half_11_02_φ1 l ∧ half_11_02_φ1 l≤1 ∧
    0≤shiftExponents 9 half_11_02_φ1 l :=
  alternate_bounds_snoc emptyPhi (951961669/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_11_02_φ2 : Fin 2 → ℝ := Fin.snoc half_11_02_φ1 (875297077/10000000000 : ℝ)

private theorem half_11_02_total2 : total half_11_02_φ2=(913629373/5000000000 : ℝ) := by
  change total (Fin.snoc half_11_02_φ1 (875297077/10000000000 : ℝ))=(913629373/5000000000 : ℝ)
  rw [alternate_total_snoc,half_11_02_total1]
  norm_num

private theorem half_11_02_bounds2 : ∀ l,0≤half_11_02_φ2 l ∧ half_11_02_φ2 l≤1 ∧
    0≤shiftExponents 9 half_11_02_φ2 l :=
  alternate_bounds_snoc half_11_02_φ1 (875297077/10000000000 : ℝ) half_11_02_bounds1 (by norm_num)

private def half_11_02_φ3 : Fin 3 → ℝ := Fin.snoc half_11_02_φ2 (792237539/10000000000 : ℝ)

private theorem half_11_02_total3 : total half_11_02_φ3=(523899257/2000000000 : ℝ) := by
  change total (Fin.snoc half_11_02_φ2 (792237539/10000000000 : ℝ))=(523899257/2000000000 : ℝ)
  rw [alternate_total_snoc,half_11_02_total2]
  norm_num

private theorem half_11_02_bounds3 : ∀ l,0≤half_11_02_φ3 l ∧ half_11_02_φ3 l≤1 ∧
    0≤shiftExponents 9 half_11_02_φ3 l :=
  alternate_bounds_snoc half_11_02_φ2 (792237539/10000000000 : ℝ) half_11_02_bounds2 (by norm_num)

private def half_11_02_φ4 : Fin 4 → ℝ := Fin.snoc half_11_02_φ3 (319007297/5000000000 : ℝ)

private theorem half_11_02_total4 : total half_11_02_φ4=(3257510879/10000000000 : ℝ) := by
  change total (Fin.snoc half_11_02_φ3 (319007297/5000000000 : ℝ))=(3257510879/10000000000 : ℝ)
  rw [alternate_total_snoc,half_11_02_total3]
  norm_num

private theorem half_11_02_bounds4 : ∀ l,0≤half_11_02_φ4 l ∧ half_11_02_φ4 l≤1 ∧
    0≤shiftExponents 9 half_11_02_φ4 l :=
  alternate_bounds_snoc half_11_02_φ3 (319007297/5000000000 : ℝ) half_11_02_bounds3 (by norm_num)

private theorem half_11_02_prefix : PrefixCondition 9 half_11_02_φ4 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_11_02_φ1, half_11_02_φ2, half_11_02_φ3, half_11_02_φ4, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_11_02_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 16 half_11_02_φ4) (7727467363/1250000000 : ℝ) := by
  have h := padded_dyadic_divisor_power (k := 9) (j := 4) (r := 0) (n := 1) (D := 16)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_02_φ4
    (fun i => (half_11_02_bounds4 i).1) (fun i => (half_11_02_bounds4 i).2.1)
    (fun i => (half_11_02_bounds4 i).2.2) half_11_02_prefix
  convert h using 1 <;> norm_num [half_11_02_total1, half_11_02_total2, half_11_02_total3, half_11_02_total4, parameterExponent, curveLoss, dyadicExponent]

private theorem half_11_02_hx4 : SourcePowerBound
    (powerBoxCross 9 7 16 half_11_02_φ4) (74536471851/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 7) (r := 2) (v := 9) (w := 10) (D := 16)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_11_02_φ4 (by norm_num [half_11_02_total1, half_11_02_total2, half_11_02_total3, half_11_02_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_11_02_total1, half_11_02_total2, half_11_02_total3, half_11_02_total4, parameterExponent, curveLoss, dyadicExponent]) half_11_02_hF2
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_10_02)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_02_total1, half_11_02_total2, half_11_02_total3, half_11_02_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_11_02_hx3 : SourcePowerBound
    (powerBoxCross 9 8 8 half_11_02_φ3) (87055986481/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 8) (u := 6) (t := 9)
    (D := 8) (ψ := (319007297/5000000000 : ℝ)) half_11_02_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_11_02_bounds3 l).1) (fun l => (half_11_02_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_11_02_total1, half_11_02_total2, half_11_02_total3, half_11_02_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_7) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_11_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_11_02_hx4)
  exact h.weaken (by norm_num [half_11_02_total1, half_11_02_total2, half_11_02_total3, half_11_02_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_11_02_hx2 : SourcePowerBound
    (powerBoxCross 9 9 4 half_11_02_φ2) (104324394219/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (792237539/10000000000 : ℝ)) half_11_02_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_11_02_bounds2 l).1) (fun l => (half_11_02_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_11_02_total1, half_11_02_total2, half_11_02_total3, half_11_02_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_02)
    (by simpa only [half_11_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_02_hx3)
  exact h.weaken (by norm_num [half_11_02_total1, half_11_02_total2, half_11_02_total3, half_11_02_total4, parameterExponent, curveLoss, dyadicExponent])

private theorem half_11_02_hx1 : SourcePowerBound
    (powerBoxCross 9 10 2 half_11_02_φ1) (25290536093/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (875297077/10000000000 : ℝ)) half_11_02_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_11_02_bounds1 l).1) (fun l => (half_11_02_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_11_02_total1, half_11_02_total2, half_11_02_total3, half_11_02_total4, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_01)
    (by simpa only [half_11_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_02_hx2)
  exact h.weaken (by norm_num [half_11_02_total1, half_11_02_total2, half_11_02_total3, half_11_02_total4, parameterExponent, curveLoss, dyadicExponent])

theorem half_11_02 : AdmissibleExponent 9 22 (9033747011/625000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 9) (ψ := (951961669/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_10_02)
    (by simpa only [half_11_02_φ1] using half_11_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_02_total1, half_11_02_total2, half_11_02_total3, half_11_02_total4, parameterExponent, curveLoss, dyadicExponent])

theorem chord_46 : AdmissibleExponent 9 24 (65022369289/4000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 24) (t := (1/2 : ℝ))
    (half_11_02) (half_13_01)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_12_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (977471943/10000000000 : ℝ)

private theorem half_12_02_total1 : total half_12_02_φ1=(977471943/10000000000 : ℝ) := by
  norm_num [half_12_02_φ1,total,emptyPhi,Fin.snoc]

private theorem half_12_02_bounds1 : ∀ l,0≤half_12_02_φ1 l ∧ half_12_02_φ1 l≤1 ∧
    0≤shiftExponents 9 half_12_02_φ1 l :=
  alternate_bounds_snoc emptyPhi (977471943/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_12_02_φ2 : Fin 2 → ℝ := Fin.snoc half_12_02_φ1 (454477607/5000000000 : ℝ)

private theorem half_12_02_total2 : total half_12_02_φ2=(1886427157/10000000000 : ℝ) := by
  change total (Fin.snoc half_12_02_φ1 (454477607/5000000000 : ℝ))=(1886427157/10000000000 : ℝ)
  rw [alternate_total_snoc,half_12_02_total1]
  norm_num

private theorem half_12_02_bounds2 : ∀ l,0≤half_12_02_φ2 l ∧ half_12_02_φ2 l≤1 ∧
    0≤shiftExponents 9 half_12_02_φ2 l :=
  alternate_bounds_snoc half_12_02_φ1 (454477607/5000000000 : ℝ) half_12_02_bounds1 (by norm_num)

private def half_12_02_φ3 : Fin 3 → ℝ := Fin.snoc half_12_02_φ2 (849604373/10000000000 : ℝ)

private theorem half_12_02_total3 : total half_12_02_φ3=(273603153/1000000000 : ℝ) := by
  change total (Fin.snoc half_12_02_φ2 (849604373/10000000000 : ℝ))=(273603153/1000000000 : ℝ)
  rw [alternate_total_snoc,half_12_02_total2]
  norm_num

private theorem half_12_02_bounds3 : ∀ l,0≤half_12_02_φ3 l ∧ half_12_02_φ3 l≤1 ∧
    0≤shiftExponents 9 half_12_02_φ3 l :=
  alternate_bounds_snoc half_12_02_φ2 (849604373/10000000000 : ℝ) half_12_02_bounds2 (by norm_num)

private def half_12_02_φ4 : Fin 4 → ℝ := Fin.snoc half_12_02_φ3 (22871741/312500000 : ℝ)

private theorem half_12_02_total4 : total half_12_02_φ4=(1733963621/5000000000 : ℝ) := by
  change total (Fin.snoc half_12_02_φ3 (22871741/312500000 : ℝ))=(1733963621/5000000000 : ℝ)
  rw [alternate_total_snoc,half_12_02_total3]
  norm_num

private theorem half_12_02_bounds4 : ∀ l,0≤half_12_02_φ4 l ∧ half_12_02_φ4 l≤1 ∧
    0≤shiftExponents 9 half_12_02_φ4 l :=
  alternate_bounds_snoc half_12_02_φ3 (22871741/312500000 : ℝ) half_12_02_bounds3 (by norm_num)

private def half_12_02_φ5 : Fin 5 → ℝ := Fin.snoc half_12_02_φ4 (462970509/10000000000 : ℝ)

private theorem half_12_02_total5 : total half_12_02_φ5=(3930897751/10000000000 : ℝ) := by
  change total (Fin.snoc half_12_02_φ4 (462970509/10000000000 : ℝ))=(3930897751/10000000000 : ℝ)
  rw [alternate_total_snoc,half_12_02_total4]
  norm_num

private theorem half_12_02_bounds5 : ∀ l,0≤half_12_02_φ5 l ∧ half_12_02_φ5 l≤1 ∧
    0≤shiftExponents 9 half_12_02_φ5 l :=
  alternate_bounds_snoc half_12_02_φ4 (462970509/10000000000 : ℝ) half_12_02_bounds4 (by norm_num)

private theorem half_12_02_prefix : PrefixCondition 9 half_12_02_φ5 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_12_02_φ1, half_12_02_φ2, half_12_02_φ3, half_12_02_φ4, half_12_02_φ5, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_12_02_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 32 half_12_02_φ5) (9457306747/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_12_02_φ5
    (fun i => (half_12_02_bounds5 i).1) (fun i => (half_12_02_bounds5 i).2.1)
    (fun i => (half_12_02_bounds5 i).2.2) half_12_02_prefix
  convert h using 1 <;> norm_num [half_12_02_total1, half_12_02_total2, half_12_02_total3, half_12_02_total4, half_12_02_total5, parameterExponent, curveLoss, dyadicExponent]

private theorem half_12_02_hx5 : SourcePowerBound
    (powerBoxCross 9 7 32 half_12_02_φ5) (36047775297/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 7) (r := 2) (v := 9) (w := 10) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_12_02_φ5 (by norm_num [half_12_02_total1, half_12_02_total2, half_12_02_total3, half_12_02_total4, half_12_02_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_12_02_total1, half_12_02_total2, half_12_02_total3, half_12_02_total4, half_12_02_total5, parameterExponent, curveLoss, dyadicExponent]) half_12_02_hF2
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_10_02)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_02_total1, half_12_02_total2, half_12_02_total3, half_12_02_total4, half_12_02_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_02_hx4 : SourcePowerBound
    (powerBoxCross 9 8 16 half_12_02_φ4) (81577193411/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 8) (u := 6) (t := 9)
    (D := 16) (ψ := (462970509/10000000000 : ℝ)) half_12_02_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_02_bounds4 l).1) (fun l => (half_12_02_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_02_total1, half_12_02_total2, half_12_02_total3, half_12_02_total4, half_12_02_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionNinthSecondSeeds.ninth_half_7) (SeedCompletionHigher9SimpleSeeds.degree9_half_9)
    (by simpa only [half_12_02_φ5, show (2:ℝ)*16=32 by norm_num] using half_12_02_hx5)
  exact h.weaken (by norm_num [half_12_02_total1, half_12_02_total2, half_12_02_total3, half_12_02_total4, half_12_02_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_02_hx3 : SourcePowerBound
    (powerBoxCross 9 9 8 half_12_02_φ3) (96696974527/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (22871741/312500000 : ℝ)) half_12_02_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_02_bounds3 l).1) (fun l => (half_12_02_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_02_total1, half_12_02_total2, half_12_02_total3, half_12_02_total4, half_12_02_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_02)
    (by simpa only [half_12_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_02_hx4)
  exact h.weaken (by norm_num [half_12_02_total1, half_12_02_total2, half_12_02_total3, half_12_02_total4, half_12_02_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_02_hx2 : SourcePowerBound
    (powerBoxCross 9 10 4 half_12_02_φ2) (58330593671/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (849604373/10000000000 : ℝ)) half_12_02_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_02_bounds2 l).1) (fun l => (half_12_02_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_02_total1, half_12_02_total2, half_12_02_total3, half_12_02_total4, half_12_02_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_02)
    (by simpa only [half_12_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_02_hx3)
  exact h.weaken (by norm_num [half_12_02_total1, half_12_02_total2, half_12_02_total3, half_12_02_total4, half_12_02_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_12_02_hx1 : SourcePowerBound
    (powerBoxCross 9 11 2 half_12_02_φ1) (70694524669/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (454477607/5000000000 : ℝ)) half_12_02_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_12_02_bounds1 l).1) (fun l => (half_12_02_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_12_02_total1, half_12_02_total2, half_12_02_total3, half_12_02_total4, half_12_02_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_02) (chord_46)
    (by simpa only [half_12_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_02_hx2)
  exact h.weaken (by norm_num [half_12_02_total1, half_12_02_total2, half_12_02_total3, half_12_02_total4, half_12_02_total5, parameterExponent, curveLoss, dyadicExponent])

theorem half_12_02 : AdmissibleExponent 9 24 (161915960141/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 10) (ψ := (977471943/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_11_02)
    (by simpa only [half_12_02_φ1] using half_12_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_02_total1, half_12_02_total2, half_12_02_total3, half_12_02_total4, half_12_02_total5, parameterExponent, curveLoss, dyadicExponent])

theorem chord_47 : AdmissibleExponent 9 26 (180358579049/10000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 26) (t := (1/2 : ℝ))
    (half_12_02) (half_14_01)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_13_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1001041779/10000000000 : ℝ)

private theorem half_13_02_total1 : total half_13_02_φ1=(1001041779/10000000000 : ℝ) := by
  norm_num [half_13_02_φ1,total,emptyPhi,Fin.snoc]

private theorem half_13_02_bounds1 : ∀ l,0≤half_13_02_φ1 l ∧ half_13_02_φ1 l≤1 ∧
    0≤shiftExponents 9 half_13_02_φ1 l :=
  alternate_bounds_snoc emptyPhi (1001041779/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_13_02_φ2 : Fin 2 → ℝ := Fin.snoc half_13_02_φ1 (935450413/10000000000 : ℝ)

private theorem half_13_02_total2 : total half_13_02_φ2=(60515381/312500000 : ℝ) := by
  change total (Fin.snoc half_13_02_φ1 (935450413/10000000000 : ℝ))=(60515381/312500000 : ℝ)
  rw [alternate_total_snoc,half_13_02_total1]
  norm_num

private theorem half_13_02_bounds2 : ∀ l,0≤half_13_02_φ2 l ∧ half_13_02_φ2 l≤1 ∧
    0≤shiftExponents 9 half_13_02_φ2 l :=
  alternate_bounds_snoc half_13_02_φ1 (935450413/10000000000 : ℝ) half_13_02_bounds1 (by norm_num)

private def half_13_02_φ3 : Fin 3 → ℝ := Fin.snoc half_13_02_φ2 (890696141/10000000000 : ℝ)

private theorem half_13_02_total3 : total half_13_02_φ3=(2827188333/10000000000 : ℝ) := by
  change total (Fin.snoc half_13_02_φ2 (890696141/10000000000 : ℝ))=(2827188333/10000000000 : ℝ)
  rw [alternate_total_snoc,half_13_02_total2]
  norm_num

private theorem half_13_02_bounds3 : ∀ l,0≤half_13_02_φ3 l ∧ half_13_02_φ3 l≤1 ∧
    0≤shiftExponents 9 half_13_02_φ3 l :=
  alternate_bounds_snoc half_13_02_φ2 (890696141/10000000000 : ℝ) half_13_02_bounds2 (by norm_num)

private def half_13_02_φ4 : Fin 4 → ℝ := Fin.snoc half_13_02_φ3 (101340417/1250000000 : ℝ)

private theorem half_13_02_total4 : total half_13_02_φ4=(3637911669/10000000000 : ℝ) := by
  change total (Fin.snoc half_13_02_φ3 (101340417/1250000000 : ℝ))=(3637911669/10000000000 : ℝ)
  rw [alternate_total_snoc,half_13_02_total3]
  norm_num

private theorem half_13_02_bounds4 : ∀ l,0≤half_13_02_φ4 l ∧ half_13_02_φ4 l≤1 ∧
    0≤shiftExponents 9 half_13_02_φ4 l :=
  alternate_bounds_snoc half_13_02_φ3 (101340417/1250000000 : ℝ) half_13_02_bounds3 (by norm_num)

private def half_13_02_φ5 : Fin 5 → ℝ := Fin.snoc half_13_02_φ4 (634348189/10000000000 : ℝ)

private theorem half_13_02_total5 : total half_13_02_φ5=(2136129929/5000000000 : ℝ) := by
  change total (Fin.snoc half_13_02_φ4 (634348189/10000000000 : ℝ))=(2136129929/5000000000 : ℝ)
  rw [alternate_total_snoc,half_13_02_total4]
  norm_num

private theorem half_13_02_bounds5 : ∀ l,0≤half_13_02_φ5 l ∧ half_13_02_φ5 l≤1 ∧
    0≤shiftExponents 9 half_13_02_φ5 l :=
  alternate_bounds_snoc half_13_02_φ4 (634348189/10000000000 : ℝ) half_13_02_bounds4 (by norm_num)

private theorem half_13_02_prefix : PrefixCondition 9 half_13_02_φ5 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_13_02_φ1, half_13_02_φ2, half_13_02_φ3, half_13_02_φ4, half_13_02_φ5, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_13_02_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 32 half_13_02_φ5) (4216610213/625000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 5) (r := 0) (n := 1) (D := 32)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_13_02_φ5
    (fun i => (half_13_02_bounds5 i).1) (fun i => (half_13_02_bounds5 i).2.1)
    (fun i => (half_13_02_bounds5 i).2.2) half_13_02_prefix
  convert h using 1 <;> norm_num [half_13_02_total1, half_13_02_total2, half_13_02_total3, half_13_02_total4, half_13_02_total5, parameterExponent, curveLoss, dyadicExponent]

private theorem half_13_02_hx5 : SourcePowerBound
    (powerBoxCross 9 8 32 half_13_02_φ5) (38269926521/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 8) (r := 2) (v := 10) (w := 11) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_13_02_φ5 (by norm_num [half_13_02_total1, half_13_02_total2, half_13_02_total3, half_13_02_total4, half_13_02_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_13_02_total1, half_13_02_total2, half_13_02_total3, half_13_02_total4, half_13_02_total5, parameterExponent, curveLoss, dyadicExponent]) half_13_02_hF2
    (half_10_02) (half_11_02)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_02_total1, half_13_02_total2, half_13_02_total3, half_13_02_total4, half_13_02_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_02_hx4 : SourcePowerBound
    (powerBoxCross 9 9 16 half_13_02_φ4) (89082802307/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 9) (u := 7) (t := 10)
    (D := 16) (ψ := (634348189/10000000000 : ℝ)) half_13_02_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_02_bounds4 l).1) (fun l => (half_13_02_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_02_total1, half_13_02_total2, half_13_02_total3, half_13_02_total4, half_13_02_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_02)
    (by simpa only [half_13_02_φ5, show (2:ℝ)*16=32 by norm_num] using half_13_02_hx5)
  exact h.weaken (by norm_num [half_13_02_total1, half_13_02_total2, half_13_02_total3, half_13_02_total4, half_13_02_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_02_hx3 : SourcePowerBound
    (powerBoxCross 9 10 8 half_13_02_φ3) (6685105559/625000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (101340417/1250000000 : ℝ)) half_13_02_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_02_bounds3 l).1) (fun l => (half_13_02_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_02_total1, half_13_02_total2, half_13_02_total3, half_13_02_total4, half_13_02_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_02)
    (by simpa only [half_13_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_02_hx4)
  exact h.weaken (by norm_num [half_13_02_total1, half_13_02_total2, half_13_02_total3, half_13_02_total4, half_13_02_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_02_hx2 : SourcePowerBound
    (powerBoxCross 9 11 4 half_13_02_φ2) (64738509743/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (890696141/10000000000 : ℝ)) half_13_02_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_02_bounds2 l).1) (fun l => (half_13_02_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_02_total1, half_13_02_total2, half_13_02_total3, half_13_02_total4, half_13_02_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_02) (half_12_02)
    (by simpa only [half_13_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_02_hx3)
  exact h.weaken (by norm_num [half_13_02_total1, half_13_02_total2, half_13_02_total3, half_13_02_total4, half_13_02_total5, parameterExponent, curveLoss, dyadicExponent])

private theorem half_13_02_hx1 : SourcePowerBound
    (powerBoxCross 9 12 2 half_13_02_φ1) (156708537847/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (935450413/10000000000 : ℝ)) half_13_02_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_13_02_bounds1 l).1) (fun l => (half_13_02_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_13_02_total1, half_13_02_total2, half_13_02_total3, half_13_02_total4, half_13_02_total5, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_02) (chord_47)
    (by simpa only [half_13_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_02_hx2)
  exact h.weaken (by norm_num [half_13_02_total1, half_13_02_total2, half_13_02_total3, half_13_02_total4, half_13_02_total5, parameterExponent, curveLoss, dyadicExponent])

theorem half_13_02 : AdmissibleExponent 9 26 (44933124691/2500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 11) (ψ := (1001041779/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_12_02)
    (by simpa only [half_13_02_φ1] using half_13_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_02_total1, half_13_02_total2, half_13_02_total3, half_13_02_total4, half_13_02_total5, parameterExponent, curveLoss, dyadicExponent])

theorem chord_48 : AdmissibleExponent 9 28 (595541386859/30000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 28) (t := (2/3 : ℝ))
    (half_13_02) (half_16_01)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_14_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (510310127/5000000000 : ℝ)

private theorem half_14_02_total1 : total half_14_02_φ1=(510310127/5000000000 : ℝ) := by
  norm_num [half_14_02_φ1,total,emptyPhi,Fin.snoc]

private theorem half_14_02_bounds1 : ∀ l,0≤half_14_02_φ1 l ∧ half_14_02_φ1 l≤1 ∧
    0≤shiftExponents 9 half_14_02_φ1 l :=
  alternate_bounds_snoc emptyPhi (510310127/5000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_14_02_φ2 : Fin 2 → ℝ := Fin.snoc half_14_02_φ1 (192225493/2000000000 : ℝ)

private theorem half_14_02_total2 : total half_14_02_φ2=(1981747719/10000000000 : ℝ) := by
  change total (Fin.snoc half_14_02_φ1 (192225493/2000000000 : ℝ))=(1981747719/10000000000 : ℝ)
  rw [alternate_total_snoc,half_14_02_total1]
  norm_num

private theorem half_14_02_bounds2 : ∀ l,0≤half_14_02_φ2 l ∧ half_14_02_φ2 l≤1 ∧
    0≤shiftExponents 9 half_14_02_φ2 l :=
  alternate_bounds_snoc half_14_02_φ1 (192225493/2000000000 : ℝ) half_14_02_bounds1 (by norm_num)

private def half_14_02_φ3 : Fin 3 → ℝ := Fin.snoc half_14_02_φ2 (920628329/10000000000 : ℝ)

private theorem half_14_02_total3 : total half_14_02_φ3=(181398503/625000000 : ℝ) := by
  change total (Fin.snoc half_14_02_φ2 (920628329/10000000000 : ℝ))=(181398503/625000000 : ℝ)
  rw [alternate_total_snoc,half_14_02_total2]
  norm_num

private theorem half_14_02_bounds3 : ∀ l,0≤half_14_02_φ3 l ∧ half_14_02_φ3 l≤1 ∧
    0≤shiftExponents 9 half_14_02_φ3 l :=
  alternate_bounds_snoc half_14_02_φ2 (920628329/10000000000 : ℝ) half_14_02_bounds2 (by norm_num)

private def half_14_02_φ4 : Fin 4 → ℝ := Fin.snoc half_14_02_φ3 (430172487/5000000000 : ℝ)

private theorem half_14_02_total4 : total half_14_02_φ4=(1881360511/5000000000 : ℝ) := by
  change total (Fin.snoc half_14_02_φ3 (430172487/5000000000 : ℝ))=(1881360511/5000000000 : ℝ)
  rw [alternate_total_snoc,half_14_02_total3]
  norm_num

private theorem half_14_02_bounds4 : ∀ l,0≤half_14_02_φ4 l ∧ half_14_02_φ4 l≤1 ∧
    0≤shiftExponents 9 half_14_02_φ4 l :=
  alternate_bounds_snoc half_14_02_φ3 (430172487/5000000000 : ℝ) half_14_02_bounds3 (by norm_num)

private def half_14_02_φ5 : Fin 5 → ℝ := Fin.snoc half_14_02_φ4 (740051913/10000000000 : ℝ)

private theorem half_14_02_total5 : total half_14_02_φ5=(900554587/2000000000 : ℝ) := by
  change total (Fin.snoc half_14_02_φ4 (740051913/10000000000 : ℝ))=(900554587/2000000000 : ℝ)
  rw [alternate_total_snoc,half_14_02_total4]
  norm_num

private theorem half_14_02_bounds5 : ∀ l,0≤half_14_02_φ5 l ∧ half_14_02_φ5 l≤1 ∧
    0≤shiftExponents 9 half_14_02_φ5 l :=
  alternate_bounds_snoc half_14_02_φ4 (740051913/10000000000 : ℝ) half_14_02_bounds4 (by norm_num)

private def half_14_02_φ6 : Fin 6 → ℝ := Fin.snoc half_14_02_φ5 (89369597/2000000000 : ℝ)

private theorem half_14_02_total6 : total half_14_02_φ6=(123740523/250000000 : ℝ) := by
  change total (Fin.snoc half_14_02_φ5 (89369597/2000000000 : ℝ))=(123740523/250000000 : ℝ)
  rw [alternate_total_snoc,half_14_02_total5]
  norm_num

private theorem half_14_02_bounds6 : ∀ l,0≤half_14_02_φ6 l ∧ half_14_02_φ6 l≤1 ∧
    0≤shiftExponents 9 half_14_02_φ6 l :=
  alternate_bounds_snoc half_14_02_φ5 (89369597/2000000000 : ℝ) half_14_02_bounds5 (by norm_num)

private theorem half_14_02_prefix : PrefixCondition 9 half_14_02_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_14_02_φ1, half_14_02_φ2, half_14_02_φ3, half_14_02_φ4, half_14_02_φ5, half_14_02_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_14_02_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_14_02_φ6) (253778431/31250000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_14_02_φ6
    (fun i => (half_14_02_bounds6 i).1) (fun i => (half_14_02_bounds6 i).2.1)
    (fun i => (half_14_02_bounds6 i).2.2) half_14_02_prefix
  convert h using 1 <;> norm_num [half_14_02_total1, half_14_02_total2, half_14_02_total3, half_14_02_total4, half_14_02_total5, half_14_02_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_14_02_hF1 : SourcePowerBound
    (paddedMoment 9 0 1 64 half_14_02_φ6) (95009477/31250000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_14_02_φ6
    (fun i => (half_14_02_bounds6 i).1) (fun i => (half_14_02_bounds6 i).2.1)
    (fun i => (half_14_02_bounds6 i).2.2) half_14_02_prefix
  convert h using 1 <;> norm_num [half_14_02_total1, half_14_02_total2, half_14_02_total3, half_14_02_total4, half_14_02_total5, half_14_02_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_14_02_hx6 : SourcePowerBound
    (powerBoxCross 9 8 64 half_14_02_φ6) (18232034129/2500000000 : ℝ) := by
  have h := full_B_cross_power (k := 9) (s := 8) (r := 1) (v := 2) (t := 11) (D := 64)
    (a := (1/22 : ℝ)) (b := (5/22 : ℝ)) (c := (8/11 : ℝ))
    (by norm_num) half_14_02_φ6 (by norm_num [half_14_02_total1, half_14_02_total2, half_14_02_total3, half_14_02_total4, half_14_02_total5, half_14_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_14_02_total1, half_14_02_total2, half_14_02_total3, half_14_02_total4, half_14_02_total5, half_14_02_total6, parameterExponent, curveLoss, dyadicExponent]) half_14_02_hF1 half_14_02_hF2
    (half_11_02)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_02_total1, half_14_02_total2, half_14_02_total3, half_14_02_total4, half_14_02_total5, half_14_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_02_hx5 : SourcePowerBound
    (powerBoxCross 9 9 32 half_14_02_φ5) (20472787621/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 9) (u := 7) (t := 10)
    (D := 32) (ψ := (89369597/2000000000 : ℝ)) half_14_02_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_02_bounds5 l).1) (fun l => (half_14_02_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_02_total1, half_14_02_total2, half_14_02_total3, half_14_02_total4, half_14_02_total5, half_14_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_8) (half_10_02)
    (by simpa only [half_14_02_φ6, show (2:ℝ)*32=64 by norm_num] using half_14_02_hx6)
  exact h.weaken (by norm_num [half_14_02_total1, half_14_02_total2, half_14_02_total3, half_14_02_total4, half_14_02_total5, half_14_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_02_hx4 : SourcePowerBound
    (powerBoxCross 9 10 16 half_14_02_φ4) (48630966337/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (740051913/10000000000 : ℝ)) half_14_02_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_02_bounds4 l).1) (fun l => (half_14_02_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_02_total1, half_14_02_total2, half_14_02_total3, half_14_02_total4, half_14_02_total5, half_14_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_02)
    (by simpa only [half_14_02_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_02_hx5)
  exact h.weaken (by norm_num [half_14_02_total1, half_14_02_total2, half_14_02_total3, half_14_02_total4, half_14_02_total5, half_14_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_02_hx3 : SourcePowerBound
    (powerBoxCross 9 11 8 half_14_02_φ3) (29413917311/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (430172487/5000000000 : ℝ)) half_14_02_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_02_bounds3 l).1) (fun l => (half_14_02_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_02_total1, half_14_02_total2, half_14_02_total3, half_14_02_total4, half_14_02_total5, half_14_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_02) (half_12_02)
    (by simpa only [half_14_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_02_hx4)
  exact h.weaken (by norm_num [half_14_02_total1, half_14_02_total2, half_14_02_total3, half_14_02_total4, half_14_02_total5, half_14_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_02_hx2 : SourcePowerBound
    (powerBoxCross 9 12 4 half_14_02_φ2) (14262446711/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (920628329/10000000000 : ℝ)) half_14_02_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_02_bounds2 l).1) (fun l => (half_14_02_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_02_total1, half_14_02_total2, half_14_02_total3, half_14_02_total4, half_14_02_total5, half_14_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_02) (half_13_02)
    (by simpa only [half_14_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_02_hx3)
  exact h.weaken (by norm_num [half_14_02_total1, half_14_02_total2, half_14_02_total3, half_14_02_total4, half_14_02_total5, half_14_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_14_02_hx1 : SourcePowerBound
    (powerBoxCross 9 13 2 half_14_02_φ1) (172409256171/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (192225493/2000000000 : ℝ)) half_14_02_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_14_02_bounds1 l).1) (fun l => (half_14_02_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_14_02_total1, half_14_02_total2, half_14_02_total3, half_14_02_total4, half_14_02_total5, half_14_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_02) (chord_48)
    (by simpa only [half_14_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_02_hx2)
  exact h.weaken (by norm_num [half_14_02_total1, half_14_02_total2, half_14_02_total3, half_14_02_total4, half_14_02_total5, half_14_02_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_14_02 : AdmissibleExponent 9 28 (197924762521/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 12) (ψ := (510310127/5000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_13_02)
    (by simpa only [half_14_02_φ1] using half_14_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_02_total1, half_14_02_total2, half_14_02_total3, half_14_02_total4, half_14_02_total5, half_14_02_total6, parameterExponent, curveLoss, dyadicExponent])

theorem chord_50 : AdmissibleExponent 9 30 (650919014881/30000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 30) (t := (2/3 : ℝ))
    (half_14_02) (half_17_01)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_15_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (41477467/400000000 : ℝ)

private theorem half_15_02_total1 : total half_15_02_φ1=(41477467/400000000 : ℝ) := by
  norm_num [half_15_02_φ1,total,emptyPhi,Fin.snoc]

private theorem half_15_02_bounds1 : ∀ l,0≤half_15_02_φ1 l ∧ half_15_02_φ1 l≤1 ∧
    0≤shiftExponents 9 half_15_02_φ1 l :=
  alternate_bounds_snoc emptyPhi (41477467/400000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_15_02_φ2 : Fin 2 → ℝ := Fin.snoc half_15_02_φ1 (983915149/10000000000 : ℝ)

private theorem half_15_02_total2 : total half_15_02_φ2=(126303239/625000000 : ℝ) := by
  change total (Fin.snoc half_15_02_φ1 (983915149/10000000000 : ℝ))=(126303239/625000000 : ℝ)
  rw [alternate_total_snoc,half_15_02_total1]
  norm_num

private theorem half_15_02_bounds2 : ∀ l,0≤half_15_02_φ2 l ∧ half_15_02_φ2 l≤1 ∧
    0≤shiftExponents 9 half_15_02_φ2 l :=
  alternate_bounds_snoc half_15_02_φ1 (983915149/10000000000 : ℝ) half_15_02_bounds1 (by norm_num)

private def half_15_02_φ3 : Fin 3 → ℝ := Fin.snoc half_15_02_φ2 (237266029/2500000000 : ℝ)

private theorem half_15_02_total3 : total half_15_02_φ3=(148495797/500000000 : ℝ) := by
  change total (Fin.snoc half_15_02_φ2 (237266029/2500000000 : ℝ))=(148495797/500000000 : ℝ)
  rw [alternate_total_snoc,half_15_02_total2]
  norm_num

private theorem half_15_02_bounds3 : ∀ l,0≤half_15_02_φ3 l ∧ half_15_02_φ3 l≤1 ∧
    0≤shiftExponents 9 half_15_02_φ3 l :=
  alternate_bounds_snoc half_15_02_φ2 (237266029/2500000000 : ℝ) half_15_02_bounds2 (by norm_num)

private def half_15_02_φ4 : Fin 4 → ℝ := Fin.snoc half_15_02_φ3 (878760507/10000000000 : ℝ)

private theorem half_15_02_total4 : total half_15_02_φ4=(3848676447/10000000000 : ℝ) := by
  change total (Fin.snoc half_15_02_φ3 (878760507/10000000000 : ℝ))=(3848676447/10000000000 : ℝ)
  rw [alternate_total_snoc,half_15_02_total3]
  norm_num

private theorem half_15_02_bounds4 : ∀ l,0≤half_15_02_φ4 l ∧ half_15_02_φ4 l≤1 ∧
    0≤shiftExponents 9 half_15_02_φ4 l :=
  alternate_bounds_snoc half_15_02_φ3 (878760507/10000000000 : ℝ) half_15_02_bounds3 (by norm_num)

private def half_15_02_φ5 : Fin 5 → ℝ := Fin.snoc half_15_02_φ4 (768915443/10000000000 : ℝ)

private theorem half_15_02_total5 : total half_15_02_φ5=(461759189/1000000000 : ℝ) := by
  change total (Fin.snoc half_15_02_φ4 (768915443/10000000000 : ℝ))=(461759189/1000000000 : ℝ)
  rw [alternate_total_snoc,half_15_02_total4]
  norm_num

private theorem half_15_02_bounds5 : ∀ l,0≤half_15_02_φ5 l ∧ half_15_02_φ5 l≤1 ∧
    0≤shiftExponents 9 half_15_02_φ5 l :=
  alternate_bounds_snoc half_15_02_φ4 (768915443/10000000000 : ℝ) half_15_02_bounds4 (by norm_num)

private def half_15_02_φ6 : Fin 6 → ℝ := Fin.snoc half_15_02_φ5 (577916317/10000000000 : ℝ)

private theorem half_15_02_total6 : total half_15_02_φ6=(5195508207/10000000000 : ℝ) := by
  change total (Fin.snoc half_15_02_φ5 (577916317/10000000000 : ℝ))=(5195508207/10000000000 : ℝ)
  rw [alternate_total_snoc,half_15_02_total5]
  norm_num

private theorem half_15_02_bounds6 : ∀ l,0≤half_15_02_φ6 l ∧ half_15_02_φ6 l≤1 ∧
    0≤shiftExponents 9 half_15_02_φ6 l :=
  alternate_bounds_snoc half_15_02_φ5 (577916317/10000000000 : ℝ) half_15_02_bounds5 (by norm_num)

private theorem half_15_02_prefix : PrefixCondition 9 half_15_02_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_15_02_φ1, half_15_02_φ2, half_15_02_φ3, half_15_02_φ4, half_15_02_φ5, half_15_02_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_15_02_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_15_02_φ6) (9413475379/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_15_02_φ6
    (fun i => (half_15_02_bounds6 i).1) (fun i => (half_15_02_bounds6 i).2.1)
    (fun i => (half_15_02_bounds6 i).2.2) half_15_02_prefix
  convert h using 1 <;> norm_num [half_15_02_total1, half_15_02_total2, half_15_02_total3, half_15_02_total4, half_15_02_total5, half_15_02_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_15_02_hx6 : SourcePowerBound
    (powerBoxCross 9 9 64 half_15_02_φ6) (38585621691/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 9) (r := 2) (v := 0) (w := 12) (D := 64)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_15_02_φ6 (by norm_num [half_15_02_total1, half_15_02_total2, half_15_02_total3, half_15_02_total4, half_15_02_total5, half_15_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_15_02_total1, half_15_02_total2, half_15_02_total3, half_15_02_total4, half_15_02_total5, half_15_02_total6, parameterExponent, curveLoss, dyadicExponent]) half_15_02_hF2
    (admissibleExponent_zero 9) (half_12_02)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_02_total1, half_15_02_total2, half_15_02_total3, half_15_02_total4, half_15_02_total5, half_15_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_02_hx5 : SourcePowerBound
    (powerBoxCross 9 10 32 half_15_02_φ5) (11115774171/1250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 10) (u := 8) (t := 11)
    (D := 32) (ψ := (577916317/10000000000 : ℝ)) half_15_02_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_02_bounds5 l).1) (fun l => (half_15_02_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_02_total1, half_15_02_total2, half_15_02_total3, half_15_02_total4, half_15_02_total5, half_15_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (SeedCompletionHigher9SimpleSeeds.degree9_half_9) (half_11_02)
    (by simpa only [half_15_02_φ6, show (2:ℝ)*32=64 by norm_num] using half_15_02_hx6)
  exact h.weaken (by norm_num [half_15_02_total1, half_15_02_total2, half_15_02_total3, half_15_02_total4, half_15_02_total5, half_15_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_02_hx4 : SourcePowerBound
    (powerBoxCross 9 11 16 half_15_02_φ4) (53086480283/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (768915443/10000000000 : ℝ)) half_15_02_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_02_bounds4 l).1) (fun l => (half_15_02_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_02_total1, half_15_02_total2, half_15_02_total3, half_15_02_total4, half_15_02_total5, half_15_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_02) (half_12_02)
    (by simpa only [half_15_02_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_02_hx5)
  exact h.weaken (by norm_num [half_15_02_total1, half_15_02_total2, half_15_02_total3, half_15_02_total4, half_15_02_total5, half_15_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_02_hx3 : SourcePowerBound
    (powerBoxCross 9 12 8 half_15_02_φ3) (64305265289/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (878760507/10000000000 : ℝ)) half_15_02_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_02_bounds3 l).1) (fun l => (half_15_02_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_02_total1, half_15_02_total2, half_15_02_total3, half_15_02_total4, half_15_02_total5, half_15_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_02) (half_13_02)
    (by simpa only [half_15_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_02_hx4)
  exact h.weaken (by norm_num [half_15_02_total1, half_15_02_total2, half_15_02_total3, half_15_02_total4, half_15_02_total5, half_15_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_02_hx2 : SourcePowerBound
    (powerBoxCross 9 13 4 half_15_02_φ2) (3902491143/250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (237266029/2500000000 : ℝ)) half_15_02_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_02_bounds2 l).1) (fun l => (half_15_02_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_02_total1, half_15_02_total2, half_15_02_total3, half_15_02_total4, half_15_02_total5, half_15_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_02) (half_14_02)
    (by simpa only [half_15_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_02_hx3)
  exact h.weaken (by norm_num [half_15_02_total1, half_15_02_total2, half_15_02_total3, half_15_02_total4, half_15_02_total5, half_15_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_15_02_hx1 : SourcePowerBound
    (powerBoxCross 9 14 2 half_15_02_φ1) (188438154687/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (983915149/10000000000 : ℝ)) half_15_02_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_15_02_bounds1 l).1) (fun l => (half_15_02_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_15_02_total1, half_15_02_total2, half_15_02_total3, half_15_02_total4, half_15_02_total5, half_15_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_02) (chord_50)
    (by simpa only [half_15_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_02_hx2)
  exact h.weaken (by norm_num [half_15_02_total1, half_15_02_total2, half_15_02_total3, half_15_02_total4, half_15_02_total5, half_15_02_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_15_02 : AdmissibleExponent 9 30 (13527215307/625000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 13) (ψ := (41477467/400000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_14_02)
    (by simpa only [half_15_02_φ1] using half_15_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_02_total1, half_15_02_total2, half_15_02_total3, half_15_02_total4, half_15_02_total5, half_15_02_total6, parameterExponent, curveLoss, dyadicExponent])

theorem chord_52 : AdmissibleExponent 9 32 (235712773933/10000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 32) (t := (2/3 : ℝ))
    (half_15_02) (half_18_01)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_16_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (65767891/625000000 : ℝ)

private theorem half_16_02_total1 : total half_16_02_φ1=(65767891/625000000 : ℝ) := by
  norm_num [half_16_02_φ1,total,emptyPhi,Fin.snoc]

private theorem half_16_02_bounds1 : ∀ l,0≤half_16_02_φ1 l ∧ half_16_02_φ1 l≤1 ∧
    0≤shiftExponents 9 half_16_02_φ1 l :=
  alternate_bounds_snoc emptyPhi (65767891/625000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_16_02_φ2 : Fin 2 → ℝ := Fin.snoc half_16_02_φ1 (251451577/2500000000 : ℝ)

private theorem half_16_02_total2 : total half_16_02_φ2=(514523141/2500000000 : ℝ) := by
  change total (Fin.snoc half_16_02_φ1 (251451577/2500000000 : ℝ))=(514523141/2500000000 : ℝ)
  rw [alternate_total_snoc,half_16_02_total1]
  norm_num

private theorem half_16_02_bounds2 : ∀ l,0≤half_16_02_φ2 l ∧ half_16_02_φ2 l≤1 ∧
    0≤shiftExponents 9 half_16_02_φ2 l :=
  alternate_bounds_snoc half_16_02_φ1 (251451577/2500000000 : ℝ) half_16_02_bounds1 (by norm_num)

private def half_16_02_φ3 : Fin 3 → ℝ := Fin.snoc half_16_02_φ2 (48909137/500000000 : ℝ)

private theorem half_16_02_total3 : total half_16_02_φ3=(379534413/1250000000 : ℝ) := by
  change total (Fin.snoc half_16_02_φ2 (48909137/500000000 : ℝ))=(379534413/1250000000 : ℝ)
  rw [alternate_total_snoc,half_16_02_total2]
  norm_num

private theorem half_16_02_bounds3 : ∀ l,0≤half_16_02_φ3 l ∧ half_16_02_φ3 l≤1 ∧
    0≤shiftExponents 9 half_16_02_φ3 l :=
  alternate_bounds_snoc half_16_02_φ2 (48909137/500000000 : ℝ) half_16_02_bounds2 (by norm_num)

private def half_16_02_φ4 : Fin 4 → ℝ := Fin.snoc half_16_02_φ3 (435232793/5000000000 : ℝ)

private theorem half_16_02_total4 : total half_16_02_φ4=(390674089/1000000000 : ℝ) := by
  change total (Fin.snoc half_16_02_φ3 (435232793/5000000000 : ℝ))=(390674089/1000000000 : ℝ)
  rw [alternate_total_snoc,half_16_02_total3]
  norm_num

private theorem half_16_02_bounds4 : ∀ l,0≤half_16_02_φ4 l ∧ half_16_02_φ4 l≤1 ∧
    0≤shiftExponents 9 half_16_02_φ4 l :=
  alternate_bounds_snoc half_16_02_φ3 (435232793/5000000000 : ℝ) half_16_02_bounds3 (by norm_num)

private def half_16_02_φ5 : Fin 5 → ℝ := Fin.snoc half_16_02_φ4 (190414347/2500000000 : ℝ)

private theorem half_16_02_total5 : total half_16_02_φ5=(2334199139/5000000000 : ℝ) := by
  change total (Fin.snoc half_16_02_φ4 (190414347/2500000000 : ℝ))=(2334199139/5000000000 : ℝ)
  rw [alternate_total_snoc,half_16_02_total4]
  norm_num

private theorem half_16_02_bounds5 : ∀ l,0≤half_16_02_φ5 l ∧ half_16_02_φ5 l≤1 ∧
    0≤shiftExponents 9 half_16_02_φ5 l :=
  alternate_bounds_snoc half_16_02_φ4 (190414347/2500000000 : ℝ) half_16_02_bounds4 (by norm_num)

private def half_16_02_φ6 : Fin 6 → ℝ := Fin.snoc half_16_02_φ5 (333225107/5000000000 : ℝ)

private theorem half_16_02_total6 : total half_16_02_φ6=(1333712123/2500000000 : ℝ) := by
  change total (Fin.snoc half_16_02_φ5 (333225107/5000000000 : ℝ))=(1333712123/2500000000 : ℝ)
  rw [alternate_total_snoc,half_16_02_total5]
  norm_num

private theorem half_16_02_bounds6 : ∀ l,0≤half_16_02_φ6 l ∧ half_16_02_φ6 l≤1 ∧
    0≤shiftExponents 9 half_16_02_φ6 l :=
  alternate_bounds_snoc half_16_02_φ5 (333225107/5000000000 : ℝ) half_16_02_bounds5 (by norm_num)

private theorem half_16_02_prefix : PrefixCondition 9 half_16_02_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_16_02_φ1, half_16_02_φ2, half_16_02_φ3, half_16_02_φ4, half_16_02_φ5, half_16_02_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_16_02_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_16_02_φ6) (2248863631/312500000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_16_02_φ6
    (fun i => (half_16_02_bounds6 i).1) (fun i => (half_16_02_bounds6 i).2.1)
    (fun i => (half_16_02_bounds6 i).2.2) half_16_02_prefix
  convert h using 1 <;> norm_num [half_16_02_total1, half_16_02_total2, half_16_02_total3, half_16_02_total4, half_16_02_total5, half_16_02_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_16_02_hx6 : SourcePowerBound
    (powerBoxCross 9 10 64 half_16_02_φ6) (82998601039/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 10) (r := 2) (v := 13) (w := 14) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_16_02_φ6 (by norm_num [half_16_02_total1, half_16_02_total2, half_16_02_total3, half_16_02_total4, half_16_02_total5, half_16_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_16_02_total1, half_16_02_total2, half_16_02_total3, half_16_02_total4, half_16_02_total5, half_16_02_total6, parameterExponent, curveLoss, dyadicExponent]) half_16_02_hF2
    (half_13_02) (half_14_02)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_02_total1, half_16_02_total2, half_16_02_total3, half_16_02_total4, half_16_02_total5, half_16_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_02_hx5 : SourcePowerBound
    (powerBoxCross 9 11 32 half_16_02_φ5) (24330138759/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 11) (u := 9) (t := 12)
    (D := 32) (ψ := (333225107/5000000000 : ℝ)) half_16_02_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_02_bounds5 l).1) (fun l => (half_16_02_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_02_total1, half_16_02_total2, half_16_02_total3, half_16_02_total4, half_16_02_total5, half_16_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_10_02) (half_12_02)
    (by simpa only [half_16_02_φ6, show (2:ℝ)*32=64 by norm_num] using half_16_02_hx6)
  exact h.weaken (by norm_num [half_16_02_total1, half_16_02_total2, half_16_02_total3, half_16_02_total4, half_16_02_total5, half_16_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_02_hx4 : SourcePowerBound
    (powerBoxCross 9 12 16 half_16_02_φ4) (23157710161/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (190414347/2500000000 : ℝ)) half_16_02_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_02_bounds4 l).1) (fun l => (half_16_02_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_02_total1, half_16_02_total2, half_16_02_total3, half_16_02_total4, half_16_02_total5, half_16_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_02) (half_13_02)
    (by simpa only [half_16_02_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_02_hx5)
  exact h.weaken (by norm_num [half_16_02_total1, half_16_02_total2, half_16_02_total3, half_16_02_total4, half_16_02_total5, half_16_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_02_hx3 : SourcePowerBound
    (powerBoxCross 9 13 8 half_16_02_φ3) (69837103131/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (435232793/5000000000 : ℝ)) half_16_02_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_02_bounds3 l).1) (fun l => (half_16_02_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_02_total1, half_16_02_total2, half_16_02_total3, half_16_02_total4, half_16_02_total5, half_16_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_02) (half_14_02)
    (by simpa only [half_16_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_02_hx4)
  exact h.weaken (by norm_num [half_16_02_total1, half_16_02_total2, half_16_02_total3, half_16_02_total4, half_16_02_total5, half_16_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_02_hx2 : SourcePowerBound
    (powerBoxCross 9 14 4 half_16_02_φ2) (84888765297/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (48909137/500000000 : ℝ)) half_16_02_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_02_bounds2 l).1) (fun l => (half_16_02_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_02_total1, half_16_02_total2, half_16_02_total3, half_16_02_total4, half_16_02_total5, half_16_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_02) (half_15_02)
    (by simpa only [half_16_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_02_hx3)
  exact h.weaken (by norm_num [half_16_02_total1, half_16_02_total2, half_16_02_total3, half_16_02_total4, half_16_02_total5, half_16_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_16_02_hx1 : SourcePowerBound
    (powerBoxCross 9 15 2 half_16_02_φ1) (204712526779/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (251451577/2500000000 : ℝ)) half_16_02_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_16_02_bounds1 l).1) (fun l => (half_16_02_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_16_02_total1, half_16_02_total2, half_16_02_total3, half_16_02_total4, half_16_02_total5, half_16_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_02) (chord_52)
    (by simpa only [half_16_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_02_hx2)
  exact h.weaken (by norm_num [half_16_02_total1, half_16_02_total2, half_16_02_total3, half_16_02_total4, half_16_02_total5, half_16_02_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_16_02 : AdmissibleExponent 9 32 (235228828203/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 14) (ψ := (65767891/625000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_15_02)
    (by simpa only [half_16_02_φ1] using half_16_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_02_total1, half_16_02_total2, half_16_02_total3, half_16_02_total4, half_16_02_total5, half_16_02_total6, parameterExponent, curveLoss, dyadicExponent])

theorem chord_54 : AdmissibleExponent 9 34 (382054491533/15000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 34) (t := (2/3 : ℝ))
    (half_16_02) (half_19_01)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_17_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (266450207/2500000000 : ℝ)

private theorem half_17_02_total1 : total half_17_02_φ1=(266450207/2500000000 : ℝ) := by
  norm_num [half_17_02_φ1,total,emptyPhi,Fin.snoc]

private theorem half_17_02_bounds1 : ∀ l,0≤half_17_02_φ1 l ∧ half_17_02_φ1 l≤1 ∧
    0≤shiftExponents 9 half_17_02_φ1 l :=
  alternate_bounds_snoc emptyPhi (266450207/2500000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_17_02_φ2 : Fin 2 → ℝ := Fin.snoc half_17_02_φ1 (1026295173/10000000000 : ℝ)

private theorem half_17_02_total2 : total half_17_02_φ2=(2092096001/10000000000 : ℝ) := by
  change total (Fin.snoc half_17_02_φ1 (1026295173/10000000000 : ℝ))=(2092096001/10000000000 : ℝ)
  rw [alternate_total_snoc,half_17_02_total1]
  norm_num

private theorem half_17_02_bounds2 : ∀ l,0≤half_17_02_φ2 l ∧ half_17_02_φ2 l≤1 ∧
    0≤shiftExponents 9 half_17_02_φ2 l :=
  alternate_bounds_snoc half_17_02_φ1 (1026295173/10000000000 : ℝ) half_17_02_bounds1 (by norm_num)

private def half_17_02_φ3 : Fin 3 → ℝ := Fin.snoc half_17_02_φ2 (988487999/10000000000 : ℝ)

private theorem half_17_02_total3 : total half_17_02_φ3=(385073/1250000 : ℝ) := by
  change total (Fin.snoc half_17_02_φ2 (988487999/10000000000 : ℝ))=(385073/1250000 : ℝ)
  rw [alternate_total_snoc,half_17_02_total2]
  norm_num

private theorem half_17_02_bounds3 : ∀ l,0≤half_17_02_φ3 l ∧ half_17_02_φ3 l≤1 ∧
    0≤shiftExponents 9 half_17_02_φ3 l :=
  alternate_bounds_snoc half_17_02_φ2 (988487999/10000000000 : ℝ) half_17_02_bounds2 (by norm_num)

private def half_17_02_φ4 : Fin 4 → ℝ := Fin.snoc half_17_02_φ3 (864926999/10000000000 : ℝ)

private theorem half_17_02_total4 : total half_17_02_φ4=(3945510999/10000000000 : ℝ) := by
  change total (Fin.snoc half_17_02_φ3 (864926999/10000000000 : ℝ))=(3945510999/10000000000 : ℝ)
  rw [alternate_total_snoc,half_17_02_total3]
  norm_num

private theorem half_17_02_bounds4 : ∀ l,0≤half_17_02_φ4 l ∧ half_17_02_φ4 l≤1 ∧
    0≤shiftExponents 9 half_17_02_φ4 l :=
  alternate_bounds_snoc half_17_02_φ3 (864926999/10000000000 : ℝ) half_17_02_bounds3 (by norm_num)

private def half_17_02_φ5 : Fin 5 → ℝ := Fin.snoc half_17_02_φ4 (189202781/2500000000 : ℝ)

private theorem half_17_02_total5 : total half_17_02_φ5=(4702322123/10000000000 : ℝ) := by
  change total (Fin.snoc half_17_02_φ4 (189202781/2500000000 : ℝ))=(4702322123/10000000000 : ℝ)
  rw [alternate_total_snoc,half_17_02_total4]
  norm_num

private theorem half_17_02_bounds5 : ∀ l,0≤half_17_02_φ5 l ∧ half_17_02_φ5 l≤1 ∧
    0≤shiftExponents 9 half_17_02_φ5 l :=
  alternate_bounds_snoc half_17_02_φ4 (189202781/2500000000 : ℝ) half_17_02_bounds4 (by norm_num)

private def half_17_02_φ6 : Fin 6 → ℝ := Fin.snoc half_17_02_φ5 (331104867/5000000000 : ℝ)

private theorem half_17_02_total6 : total half_17_02_φ6=(5364531857/10000000000 : ℝ) := by
  change total (Fin.snoc half_17_02_φ5 (331104867/5000000000 : ℝ))=(5364531857/10000000000 : ℝ)
  rw [alternate_total_snoc,half_17_02_total5]
  norm_num

private theorem half_17_02_bounds6 : ∀ l,0≤half_17_02_φ6 l ∧ half_17_02_φ6 l≤1 ∧
    0≤shiftExponents 9 half_17_02_φ6 l :=
  alternate_bounds_snoc half_17_02_φ5 (331104867/5000000000 : ℝ) half_17_02_bounds5 (by norm_num)

private theorem half_17_02_prefix : PrefixCondition 9 half_17_02_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_17_02_φ1, half_17_02_φ2, half_17_02_φ3, half_17_02_φ4, half_17_02_φ5, half_17_02_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_17_02_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_17_02_φ6) (8906404429/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_17_02_φ6
    (fun i => (half_17_02_bounds6 i).1) (fun i => (half_17_02_bounds6 i).2.1)
    (fun i => (half_17_02_bounds6 i).2.2) half_17_02_prefix
  convert h using 1 <;> norm_num [half_17_02_total1, half_17_02_total2, half_17_02_total3, half_17_02_total4, half_17_02_total5, half_17_02_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_17_02_hx6 : SourcePowerBound
    (powerBoxCross 9 11 64 half_17_02_φ6) (45456818819/5000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 11) (r := 2) (v := 14) (w := 15) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_17_02_φ6 (by norm_num [half_17_02_total1, half_17_02_total2, half_17_02_total3, half_17_02_total4, half_17_02_total5, half_17_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_17_02_total1, half_17_02_total2, half_17_02_total3, half_17_02_total4, half_17_02_total5, half_17_02_total6, parameterExponent, curveLoss, dyadicExponent]) half_17_02_hF2
    (half_14_02) (half_15_02)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_02_total1, half_17_02_total2, half_17_02_total3, half_17_02_total4, half_17_02_total5, half_17_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_02_hx5 : SourcePowerBound
    (powerBoxCross 9 12 32 half_17_02_φ5) (53104488329/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 12) (u := 10) (t := 13)
    (D := 32) (ψ := (331104867/5000000000 : ℝ)) half_17_02_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_02_bounds5 l).1) (fun l => (half_17_02_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_02_total1, half_17_02_total2, half_17_02_total3, half_17_02_total4, half_17_02_total5, half_17_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_11_02) (half_13_02)
    (by simpa only [half_17_02_φ6, show (2:ℝ)*32=64 by norm_num] using half_17_02_hx6)
  exact h.weaken (by norm_num [half_17_02_total1, half_17_02_total2, half_17_02_total3, half_17_02_total4, half_17_02_total5, half_17_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_02_hx4 : SourcePowerBound
    (powerBoxCross 9 13 16 half_17_02_φ4) (25188487429/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (189202781/2500000000 : ℝ)) half_17_02_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_02_bounds4 l).1) (fun l => (half_17_02_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_02_total1, half_17_02_total2, half_17_02_total3, half_17_02_total4, half_17_02_total5, half_17_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_02) (half_14_02)
    (by simpa only [half_17_02_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_02_hx5)
  exact h.weaken (by norm_num [half_17_02_total1, half_17_02_total2, half_17_02_total3, half_17_02_total4, half_17_02_total5, half_17_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_02_hx3 : SourcePowerBound
    (powerBoxCross 9 14 8 half_17_02_φ3) (30268162817/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (864926999/10000000000 : ℝ)) half_17_02_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_02_bounds3 l).1) (fun l => (half_17_02_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_02_total1, half_17_02_total2, half_17_02_total3, half_17_02_total4, half_17_02_total5, half_17_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_02) (half_15_02)
    (by simpa only [half_17_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_02_hx4)
  exact h.weaken (by norm_num [half_17_02_total1, half_17_02_total2, half_17_02_total3, half_17_02_total4, half_17_02_total5, half_17_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_02_hx2 : SourcePowerBound
    (powerBoxCross 9 15 4 half_17_02_φ2) (183654960587/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (988487999/10000000000 : ℝ)) half_17_02_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_02_bounds2 l).1) (fun l => (half_17_02_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_02_total1, half_17_02_total2, half_17_02_total3, half_17_02_total4, half_17_02_total5, half_17_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_02) (half_16_02)
    (by simpa only [half_17_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_02_hx3)
  exact h.weaken (by norm_num [half_17_02_total1, half_17_02_total2, half_17_02_total3, half_17_02_total4, half_17_02_total5, half_17_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_17_02_hx1 : SourcePowerBound
    (powerBoxCross 9 16 2 half_17_02_φ1) (110611960527/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (1026295173/10000000000 : ℝ)) half_17_02_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_17_02_bounds1 l).1) (fun l => (half_17_02_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_17_02_total1, half_17_02_total2, half_17_02_total3, half_17_02_total4, half_17_02_total5, half_17_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_02) (chord_54)
    (by simpa only [half_17_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_02_hx2)
  exact h.weaken (by norm_num [half_17_02_total1, half_17_02_total2, half_17_02_total3, half_17_02_total4, half_17_02_total5, half_17_02_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_17_02 : AdmissibleExponent 9 34 (127131873361/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 15) (ψ := (266450207/2500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_16_02)
    (by simpa only [half_17_02_φ1] using half_17_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_02_total1, half_17_02_total2, half_17_02_total3, half_17_02_total4, half_17_02_total5, half_17_02_total6, parameterExponent, curveLoss, dyadicExponent])

theorem chord_56 : AdmissibleExponent 9 36 (410871900179/15000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 36) (t := (2/3 : ℝ))
    (half_17_02) (half_20_01)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_18_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1077612873/10000000000 : ℝ)

private theorem half_18_02_total1 : total half_18_02_φ1=(1077612873/10000000000 : ℝ) := by
  norm_num [half_18_02_φ1,total,emptyPhi,Fin.snoc]

private theorem half_18_02_bounds1 : ∀ l,0≤half_18_02_φ1 l ∧ half_18_02_φ1 l≤1 ∧
    0≤shiftExponents 9 half_18_02_φ1 l :=
  alternate_bounds_snoc emptyPhi (1077612873/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_18_02_φ2 : Fin 2 → ℝ := Fin.snoc half_18_02_φ1 (8349509/80000000 : ℝ)

private theorem half_18_02_total2 : total half_18_02_φ2=(1060650749/5000000000 : ℝ) := by
  change total (Fin.snoc half_18_02_φ1 (8349509/80000000 : ℝ))=(1060650749/5000000000 : ℝ)
  rw [alternate_total_snoc,half_18_02_total1]
  norm_num

private theorem half_18_02_bounds2 : ∀ l,0≤half_18_02_φ2 l ∧ half_18_02_φ2 l≤1 ∧
    0≤shiftExponents 9 half_18_02_φ2 l :=
  alternate_bounds_snoc half_18_02_φ1 (8349509/80000000 : ℝ) half_18_02_bounds1 (by norm_num)

private def half_18_02_φ3 : Fin 3 → ℝ := Fin.snoc half_18_02_φ2 (15388083/156250000 : ℝ)

private theorem half_18_02_total3 : total half_18_02_φ3=(310613881/1000000000 : ℝ) := by
  change total (Fin.snoc half_18_02_φ2 (15388083/156250000 : ℝ))=(310613881/1000000000 : ℝ)
  rw [alternate_total_snoc,half_18_02_total2]
  norm_num

private theorem half_18_02_bounds3 : ∀ l,0≤half_18_02_φ3 l ∧ half_18_02_φ3 l≤1 ∧
    0≤shiftExponents 9 half_18_02_φ3 l :=
  alternate_bounds_snoc half_18_02_φ2 (15388083/156250000 : ℝ) half_18_02_bounds2 (by norm_num)

private def half_18_02_φ4 : Fin 4 → ℝ := Fin.snoc half_18_02_φ3 (107716581/1250000000 : ℝ)

private theorem half_18_02_total4 : total half_18_02_φ4=(1983935729/5000000000 : ℝ) := by
  change total (Fin.snoc half_18_02_φ3 (107716581/1250000000 : ℝ))=(1983935729/5000000000 : ℝ)
  rw [alternate_total_snoc,half_18_02_total3]
  norm_num

private theorem half_18_02_bounds4 : ∀ l,0≤half_18_02_φ4 l ∧ half_18_02_φ4 l≤1 ∧
    0≤shiftExponents 9 half_18_02_φ4 l :=
  alternate_bounds_snoc half_18_02_φ3 (107716581/1250000000 : ℝ) half_18_02_bounds3 (by norm_num)

private def half_18_02_φ5 : Fin 5 → ℝ := Fin.snoc half_18_02_φ4 (754016067/10000000000 : ℝ)

private theorem half_18_02_total5 : total half_18_02_φ5=(188875501/400000000 : ℝ) := by
  change total (Fin.snoc half_18_02_φ4 (754016067/10000000000 : ℝ))=(188875501/400000000 : ℝ)
  rw [alternate_total_snoc,half_18_02_total4]
  norm_num

private theorem half_18_02_bounds5 : ∀ l,0≤half_18_02_φ5 l ∧ half_18_02_φ5 l≤1 ∧
    0≤shiftExponents 9 half_18_02_φ5 l :=
  alternate_bounds_snoc half_18_02_φ4 (754016067/10000000000 : ℝ) half_18_02_bounds4 (by norm_num)

private def half_18_02_φ6 : Fin 6 → ℝ := Fin.snoc half_18_02_φ5 (659764059/10000000000 : ℝ)

private theorem half_18_02_total6 : total half_18_02_φ6=(42044153/78125000 : ℝ) := by
  change total (Fin.snoc half_18_02_φ5 (659764059/10000000000 : ℝ))=(42044153/78125000 : ℝ)
  rw [alternate_total_snoc,half_18_02_total5]
  norm_num

private theorem half_18_02_bounds6 : ∀ l,0≤half_18_02_φ6 l ∧ half_18_02_φ6 l≤1 ∧
    0≤shiftExponents 9 half_18_02_φ6 l :=
  alternate_bounds_snoc half_18_02_φ5 (659764059/10000000000 : ℝ) half_18_02_bounds5 (by norm_num)

private theorem half_18_02_prefix : PrefixCondition 9 half_18_02_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_18_02_φ1, half_18_02_φ2, half_18_02_φ3, half_18_02_φ4, half_18_02_φ5, half_18_02_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_18_02_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_18_02_φ6) (69180041/9765625 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_18_02_φ6
    (fun i => (half_18_02_bounds6 i).1) (fun i => (half_18_02_bounds6 i).2.1)
    (fun i => (half_18_02_bounds6 i).2.2) half_18_02_prefix
  convert h using 1 <;> norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_18_02_hx6 : SourcePowerBound
    (powerBoxCross 9 12 64 half_18_02_φ6) (24796935489/2500000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 12) (r := 2) (v := 0) (w := 16) (D := 64)
    (a := (1/4 : ℝ)) (b := (0/1 : ℝ)) (c := (3/4 : ℝ))
    (by norm_num) half_18_02_φ6 (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, parameterExponent, curveLoss, dyadicExponent]) half_18_02_hF2
    (admissibleExponent_zero 9) (half_16_02)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_02_hx5 : SourcePowerBound
    (powerBoxCross 9 13 32 half_18_02_φ5) (57763532733/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 13) (u := 11) (t := 14)
    (D := 32) (ψ := (659764059/10000000000 : ℝ)) half_18_02_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_02_bounds5 l).1) (fun l => (half_18_02_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_12_02) (half_14_02)
    (by simpa only [half_18_02_φ6, show (2:ℝ)*32=64 by norm_num] using half_18_02_hx6)
  exact h.weaken (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_02_hx4 : SourcePowerBound
    (powerBoxCross 9 14 16 half_18_02_φ4) (136595568977/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 14) (u := 12) (t := 15)
    (D := 16) (ψ := (754016067/10000000000 : ℝ)) half_18_02_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_02_bounds4 l).1) (fun l => (half_18_02_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_02) (half_15_02)
    (by simpa only [half_18_02_φ5, show (2:ℝ)*16=32 by norm_num] using half_18_02_hx5)
  exact h.weaken (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_02_hx3 : SourcePowerBound
    (powerBoxCross 9 15 8 half_18_02_φ3) (163588364473/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 15) (u := 13) (t := 16)
    (D := 8) (ψ := (107716581/1250000000 : ℝ)) half_18_02_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_02_bounds3 l).1) (fun l => (half_18_02_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_02) (half_16_02)
    (by simpa only [half_18_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_18_02_hx4)
  exact h.weaken (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_02_hx2 : SourcePowerBound
    (powerBoxCross 9 16 4 half_18_02_φ2) (19775248729/1000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 16) (u := 14) (t := 17)
    (D := 4) (ψ := (15388083/156250000 : ℝ)) half_18_02_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_02_bounds2 l).1) (fun l => (half_18_02_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_02) (half_17_02)
    (by simpa only [half_18_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_18_02_hx3)
  exact h.weaken (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_18_02_hx1 : SourcePowerBound
    (powerBoxCross 9 17 2 half_18_02_φ1) (237941570941/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 17) (u := 15) (t := 18)
    (D := 2) (ψ := (8349509/80000000 : ℝ)) half_18_02_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_18_02_bounds1 l).1) (fun l => (half_18_02_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_02) (chord_56)
    (by simpa only [half_18_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_18_02_hx2)
  exact h.weaken (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_18_02 : AdmissibleExponent 9 36 (1094011183/40000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 16) (ψ := (1077612873/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_17_02)
    (by simpa only [half_18_02_φ1] using half_18_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_18_02_total1, half_18_02_total2, half_18_02_total3, half_18_02_total4, half_18_02_total5, half_18_02_total6, parameterExponent, curveLoss, dyadicExponent])

theorem chord_58 : AdmissibleExponent 9 38 (146667268479/5000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 38) (t := (2/3 : ℝ))
    (half_18_02) (half_21_01)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_19_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1088864037/10000000000 : ℝ)

private theorem half_19_02_total1 : total half_19_02_φ1=(1088864037/10000000000 : ℝ) := by
  norm_num [half_19_02_φ1,total,emptyPhi,Fin.snoc]

private theorem half_19_02_bounds1 : ∀ l,0≤half_19_02_φ1 l ∧ half_19_02_φ1 l≤1 ∧
    0≤shiftExponents 9 half_19_02_φ1 l :=
  alternate_bounds_snoc emptyPhi (1088864037/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_19_02_φ2 : Fin 2 → ℝ := Fin.snoc half_19_02_φ1 (264514609/2500000000 : ℝ)

private theorem half_19_02_total2 : total half_19_02_φ2=(2146922473/10000000000 : ℝ) := by
  change total (Fin.snoc half_19_02_φ1 (264514609/2500000000 : ℝ))=(2146922473/10000000000 : ℝ)
  rw [alternate_total_snoc,half_19_02_total1]
  norm_num

private theorem half_19_02_bounds2 : ∀ l,0≤half_19_02_φ2 l ∧ half_19_02_φ2 l≤1 ∧
    0≤shiftExponents 9 half_19_02_φ2 l :=
  alternate_bounds_snoc half_19_02_φ1 (264514609/2500000000 : ℝ) half_19_02_bounds1 (by norm_num)

private def half_19_02_φ3 : Fin 3 → ℝ := Fin.snoc half_19_02_φ2 (98163469/1000000000 : ℝ)

private theorem half_19_02_total3 : total half_19_02_φ3=(3128557163/10000000000 : ℝ) := by
  change total (Fin.snoc half_19_02_φ2 (98163469/1000000000 : ℝ))=(3128557163/10000000000 : ℝ)
  rw [alternate_total_snoc,half_19_02_total2]
  norm_num

private theorem half_19_02_bounds3 : ∀ l,0≤half_19_02_φ3 l ∧ half_19_02_φ3 l≤1 ∧
    0≤shiftExponents 9 half_19_02_φ3 l :=
  alternate_bounds_snoc half_19_02_φ2 (98163469/1000000000 : ℝ) half_19_02_bounds2 (by norm_num)

private def half_19_02_φ4 : Fin 4 → ℝ := Fin.snoc half_19_02_φ3 (429465177/5000000000 : ℝ)

private theorem half_19_02_total4 : total half_19_02_φ4=(3987487517/10000000000 : ℝ) := by
  change total (Fin.snoc half_19_02_φ3 (429465177/5000000000 : ℝ))=(3987487517/10000000000 : ℝ)
  rw [alternate_total_snoc,half_19_02_total3]
  norm_num

private theorem half_19_02_bounds4 : ∀ l,0≤half_19_02_φ4 l ∧ half_19_02_φ4 l≤1 ∧
    0≤shiftExponents 9 half_19_02_φ4 l :=
  alternate_bounds_snoc half_19_02_φ3 (429465177/5000000000 : ℝ) half_19_02_bounds3 (by norm_num)

private def half_19_02_φ5 : Fin 5 → ℝ := Fin.snoc half_19_02_φ4 (37578203/500000000 : ℝ)

private theorem half_19_02_total5 : total half_19_02_φ5=(4739051577/10000000000 : ℝ) := by
  change total (Fin.snoc half_19_02_φ4 (37578203/500000000 : ℝ))=(4739051577/10000000000 : ℝ)
  rw [alternate_total_snoc,half_19_02_total4]
  norm_num

private theorem half_19_02_bounds5 : ∀ l,0≤half_19_02_φ5 l ∧ half_19_02_φ5 l≤1 ∧
    0≤shiftExponents 9 half_19_02_φ5 l :=
  alternate_bounds_snoc half_19_02_φ4 (37578203/500000000 : ℝ) half_19_02_bounds4 (by norm_num)

private def half_19_02_φ6 : Fin 6 → ℝ := Fin.snoc half_19_02_φ5 (82202319/1250000000 : ℝ)

private theorem half_19_02_total6 : total half_19_02_φ6=(5396670129/10000000000 : ℝ) := by
  change total (Fin.snoc half_19_02_φ5 (82202319/1250000000 : ℝ))=(5396670129/10000000000 : ℝ)
  rw [alternate_total_snoc,half_19_02_total5]
  norm_num

private theorem half_19_02_bounds6 : ∀ l,0≤half_19_02_φ6 l ∧ half_19_02_φ6 l≤1 ∧
    0≤shiftExponents 9 half_19_02_φ6 l :=
  alternate_bounds_snoc half_19_02_φ5 (82202319/1250000000 : ℝ) half_19_02_bounds5 (by norm_num)

private theorem half_19_02_prefix : PrefixCondition 9 half_19_02_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_19_02_φ1, half_19_02_φ2, half_19_02_φ3, half_19_02_φ4, half_19_02_φ5, half_19_02_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_19_02_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_19_02_φ6) (8809989613/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_19_02_φ6
    (fun i => (half_19_02_bounds6 i).1) (fun i => (half_19_02_bounds6 i).2.1)
    (fun i => (half_19_02_bounds6 i).2.2) half_19_02_prefix
  convert h using 1 <;> norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_19_02_hx6 : SourcePowerBound
    (powerBoxCross 9 13 64 half_19_02_φ6) (107618563983/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 13) (r := 2) (v := 17) (w := 18) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_19_02_φ6 (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, parameterExponent, curveLoss, dyadicExponent]) half_19_02_hF2
    (half_17_02) (half_18_02)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_02_hx5 : SourcePowerBound
    (powerBoxCross 9 14 32 half_19_02_φ5) (62503046607/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 14) (u := 12) (t := 15)
    (D := 32) (ψ := (82202319/1250000000 : ℝ)) half_19_02_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_02_bounds5 l).1) (fun l => (half_19_02_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_13_02) (half_15_02)
    (by simpa only [half_19_02_φ6, show (2:ℝ)*32=64 by norm_num] using half_19_02_hx6)
  exact h.weaken (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_02_hx4 : SourcePowerBound
    (powerBoxCross 9 15 16 half_19_02_φ4) (73707512323/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 15) (u := 13) (t := 16)
    (D := 16) (ψ := (37578203/500000000 : ℝ)) half_19_02_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_02_bounds4 l).1) (fun l => (half_19_02_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_02) (half_16_02)
    (by simpa only [half_19_02_φ5, show (2:ℝ)*16=32 by norm_num] using half_19_02_hx5)
  exact h.weaken (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_02_hx3 : SourcePowerBound
    (powerBoxCross 9 16 8 half_19_02_φ3) (176005713861/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 16) (u := 14) (t := 17)
    (D := 8) (ψ := (429465177/5000000000 : ℝ)) half_19_02_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_02_bounds3 l).1) (fun l => (half_19_02_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_02) (half_17_02)
    (by simpa only [half_19_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_19_02_hx4)
  exact h.weaken (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_02_hx2 : SourcePowerBound
    (powerBoxCross 9 17 4 half_19_02_φ2) (106011218839/5000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 17) (u := 15) (t := 18)
    (D := 4) (ψ := (98163469/1000000000 : ℝ)) half_19_02_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_02_bounds2 l).1) (fun l => (half_19_02_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_02) (half_18_02)
    (by simpa only [half_19_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_19_02_hx3)
  exact h.weaken (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_19_02_hx1 : SourcePowerBound
    (powerBoxCross 9 18 2 half_19_02_φ1) (254810923959/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 18) (u := 16) (t := 19)
    (D := 2) (ψ := (264514609/2500000000 : ℝ)) half_19_02_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_19_02_bounds1 l).1) (fun l => (half_19_02_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_02) (chord_58)
    (by simpa only [half_19_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_19_02_hx2)
  exact h.weaken (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_19_02 : AdmissibleExponent 9 38 (146460582627/5000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 17) (ψ := (1088864037/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_18_02)
    (by simpa only [half_19_02_φ1] using half_19_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_19_02_total1, half_19_02_total2, half_19_02_total3, half_19_02_total4, half_19_02_total5, half_19_02_total6, parameterExponent, curveLoss, dyadicExponent])

theorem chord_60 : AdmissibleExponent 9 40 (156479796157/5000000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 40) (t := (1/2 : ℝ))
    (half_19_02) (half_21_01)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_20_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1100422253/10000000000 : ℝ)

private theorem half_20_02_total1 : total half_20_02_φ1=(1100422253/10000000000 : ℝ) := by
  norm_num [half_20_02_φ1,total,emptyPhi,Fin.snoc]

private theorem half_20_02_bounds1 : ∀ l,0≤half_20_02_φ1 l ∧ half_20_02_φ1 l≤1 ∧
    0≤shiftExponents 9 half_20_02_φ1 l :=
  alternate_bounds_snoc emptyPhi (1100422253/10000000000 : ℝ) (fun i => Fin.elim0 i) (by norm_num)

private def half_20_02_φ2 : Fin 2 → ℝ := Fin.snoc half_20_02_φ1 (1070066437/10000000000 : ℝ)

private theorem half_20_02_total2 : total half_20_02_φ2=(217048869/1000000000 : ℝ) := by
  change total (Fin.snoc half_20_02_φ1 (1070066437/10000000000 : ℝ))=(217048869/1000000000 : ℝ)
  rw [alternate_total_snoc,half_20_02_total1]
  norm_num

private theorem half_20_02_bounds2 : ∀ l,0≤half_20_02_φ2 l ∧ half_20_02_φ2 l≤1 ∧
    0≤shiftExponents 9 half_20_02_φ2 l :=
  alternate_bounds_snoc half_20_02_φ1 (1070066437/10000000000 : ℝ) half_20_02_bounds1 (by norm_num)

private def half_20_02_φ3 : Fin 3 → ℝ := Fin.snoc half_20_02_φ2 (978688913/10000000000 : ℝ)

private theorem half_20_02_total3 : total half_20_02_φ3=(3149177603/10000000000 : ℝ) := by
  change total (Fin.snoc half_20_02_φ2 (978688913/10000000000 : ℝ))=(3149177603/10000000000 : ℝ)
  rw [alternate_total_snoc,half_20_02_total2]
  norm_num

private theorem half_20_02_bounds3 : ∀ l,0≤half_20_02_φ3 l ∧ half_20_02_φ3 l≤1 ∧
    0≤shiftExponents 9 half_20_02_φ3 l :=
  alternate_bounds_snoc half_20_02_φ2 (978688913/10000000000 : ℝ) half_20_02_bounds2 (by norm_num)

private def half_20_02_φ4 : Fin 4 → ℝ := Fin.snoc half_20_02_φ3 (856352799/10000000000 : ℝ)

private theorem half_20_02_total4 : total half_20_02_φ4=(2002765201/5000000000 : ℝ) := by
  change total (Fin.snoc half_20_02_φ3 (856352799/10000000000 : ℝ))=(2002765201/5000000000 : ℝ)
  rw [alternate_total_snoc,half_20_02_total3]
  norm_num

private theorem half_20_02_bounds4 : ∀ l,0≤half_20_02_φ4 l ∧ half_20_02_φ4 l≤1 ∧
    0≤shiftExponents 9 half_20_02_φ4 l :=
  alternate_bounds_snoc half_20_02_φ3 (856352799/10000000000 : ℝ) half_20_02_bounds3 (by norm_num)

private def half_20_02_φ5 : Fin 5 → ℝ := Fin.snoc half_20_02_φ4 (749308699/10000000000 : ℝ)

private theorem half_20_02_total5 : total half_20_02_φ5=(4754839101/10000000000 : ℝ) := by
  change total (Fin.snoc half_20_02_φ4 (749308699/10000000000 : ℝ))=(4754839101/10000000000 : ℝ)
  rw [alternate_total_snoc,half_20_02_total4]
  norm_num

private theorem half_20_02_bounds5 : ∀ l,0≤half_20_02_φ5 l ∧ half_20_02_φ5 l≤1 ∧
    0≤shiftExponents 9 half_20_02_φ5 l :=
  alternate_bounds_snoc half_20_02_φ4 (749308699/10000000000 : ℝ) half_20_02_bounds4 (by norm_num)

private def half_20_02_φ6 : Fin 6 → ℝ := Fin.snoc half_20_02_φ5 (81955639/1250000000 : ℝ)

private theorem half_20_02_total6 : total half_20_02_φ6=(5410484213/10000000000 : ℝ) := by
  change total (Fin.snoc half_20_02_φ5 (81955639/1250000000 : ℝ))=(5410484213/10000000000 : ℝ)
  rw [alternate_total_snoc,half_20_02_total5]
  norm_num

private theorem half_20_02_bounds6 : ∀ l,0≤half_20_02_φ6 l ∧ half_20_02_φ6 l≤1 ∧
    0≤shiftExponents 9 half_20_02_φ6 l :=
  alternate_bounds_snoc half_20_02_φ5 (81955639/1250000000 : ℝ) half_20_02_bounds5 (by norm_num)

private theorem half_20_02_prefix : PrefixCondition 9 half_20_02_φ6 := by
  unfold PrefixCondition
  intro i hi
  interval_cases i <;> norm_num [phiExtend,half_20_02_φ1, half_20_02_φ2, half_20_02_φ3, half_20_02_φ4, half_20_02_φ5, half_20_02_φ6, emptyPhi, total, Fin.snoc, Finset.sum_range_succ]

private theorem half_20_02_hF2 : SourcePowerBound
    (paddedMoment 9 0 2 64 half_20_02_φ6) (8768547361/1250000000 : ℝ) := by
  have h := padded_dyadic_sharp_divisor_power (k := 9) (j := 6) (r := 0) (n := 1) (D := 64)
    (by norm_num) (by norm_num) (by norm_num)
    (by intro t ht; interval_cases t <;> norm_num [SharpResidual, Nat.odd_iff])
    (by norm_num) half_20_02_φ6
    (fun i => (half_20_02_bounds6 i).1) (fun i => (half_20_02_bounds6 i).2.1)
    (fun i => (half_20_02_bounds6 i).2.2) half_20_02_prefix
  convert h using 1 <;> norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, parameterExponent, curveLoss, dyadicExponent]

private theorem half_20_02_hx6 : SourcePowerBound
    (powerBoxCross 9 14 64 half_20_02_φ6) (116136545309/10000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 14) (r := 2) (v := 18) (w := 19) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_20_02_φ6 (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, parameterExponent, curveLoss, dyadicExponent]) half_20_02_hF2
    (half_18_02) (half_19_02)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_02_hx5 : SourcePowerBound
    (powerBoxCross 9 15 32 half_20_02_φ5) (134590777863/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 5) (s := 15) (u := 13) (t := 16)
    (D := 32) (ψ := (81955639/1250000000 : ℝ)) half_20_02_φ5
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_02_bounds5 l).1) (fun l => (half_20_02_bounds5 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_14_02) (half_16_02)
    (by simpa only [half_20_02_φ6, show (2:ℝ)*32=64 by norm_num] using half_20_02_hx6)
  exact h.weaken (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_02_hx4 : SourcePowerBound
    (powerBoxCross 9 16 16 half_20_02_φ4) (158347058439/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 4) (s := 16) (u := 14) (t := 17)
    (D := 16) (ψ := (749308699/10000000000 : ℝ)) half_20_02_φ4
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_02_bounds4 l).1) (fun l => (half_20_02_bounds4 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_15_02) (half_17_02)
    (by simpa only [half_20_02_φ5, show (2:ℝ)*16=32 by norm_num] using half_20_02_hx5)
  exact h.weaken (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_02_hx3 : SourcePowerBound
    (powerBoxCross 9 17 8 half_20_02_φ3) (188536241131/10000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 3) (s := 17) (u := 15) (t := 18)
    (D := 8) (ψ := (856352799/10000000000 : ℝ)) half_20_02_φ3
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_02_bounds3 l).1) (fun l => (half_20_02_bounds3 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_16_02) (half_18_02)
    (by simpa only [half_20_02_φ4, show (2:ℝ)*8=16 by norm_num] using half_20_02_hx4)
  exact h.weaken (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_02_hx2 : SourcePowerBound
    (powerBoxCross 9 18 4 half_20_02_φ2) (45281202337/2000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 18) (u := 16) (t := 19)
    (D := 4) (ψ := (978688913/10000000000 : ℝ)) half_20_02_φ2
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_02_bounds2 l).1) (fun l => (half_20_02_bounds2 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_17_02) (half_19_02)
    (by simpa only [half_20_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_20_02_hx3)
  exact h.weaken (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, parameterExponent, curveLoss, dyadicExponent])

private theorem half_20_02_hx1 : SourcePowerBound
    (powerBoxCross 9 19 2 half_20_02_φ1) (67946972663/2500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 19) (u := 17) (t := 20)
    (D := 2) (ψ := (1070066437/10000000000 : ℝ)) half_20_02_φ1
    (by norm_num) (by norm_num) (by norm_num)
    (fun l => (half_20_02_bounds1 l).1) (fun l => (half_20_02_bounds1 l).2.2)
    (by norm_num) (by norm_num) (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, parameterExponent, curveLoss, dyadicExponent]) (by norm_num)
    (half_18_02) (chord_60)
    (by simpa only [half_20_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_20_02_hx2)
  exact h.weaken (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, parameterExponent, curveLoss, dyadicExponent])

theorem half_20_02 : AdmissibleExponent 9 40 (312503514013/10000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 18) (ψ := (1100422253/10000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (half_19_02)
    (by simpa only [half_20_02_φ1] using half_20_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_20_02_total1, half_20_02_total2, half_20_02_total3, half_20_02_total4, half_20_02_total5, half_20_02_total6, parameterExponent, curveLoss, dyadicExponent])

theorem chord_61 : AdmissibleExponent 9 42 (41606385039/1250000000 : ℝ) := by
  have h := admissibleExponent_interpolation (p := 42) (t := (1/2 : ℝ))
    (half_20_02) (half_22_01)
    (by norm_num) (by norm_num) (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

end Waring.SeedCompletionAlternate9Seeds
