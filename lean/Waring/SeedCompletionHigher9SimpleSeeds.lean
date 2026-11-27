import Waring.SeedCompletionNinthSecondSeeds
import Waring.SeedCompletionGeneralTerminal
import Waring.SeedCompletionNaturalChronological

/-! # Actual degree-9 higher seeds from condition(i)

Every finite stage uses the proved padded second/fourth moments,
literal full-box Holder and the actual all-depth recurrence.
LP calculations select rational witnesses only; all inequalities,
rounding and admissibility are checked by Lean. -/
noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionHigher9SimpleSeeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges

private theorem half_8_00 : AdmissibleExponent 9 16 (12234038403403/1250000000000 : ℝ) := by
  have h := endpoint_admissible (s := 6) (by norm_num : 0 < (9 : ℕ))
    SeedCompletionNinthSecondSeeds.ninth_half_7 (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_9_00 : AdmissibleExponent 9 18 (114775384201977/10000000000000 : ℝ) := by
  have h := endpoint_admissible (s := 7) (by norm_num : 0 < (9 : ℕ))
    half_8_00 (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_8_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (892777837433/10000000000000 : ℝ)

private def half_8_01_φ2 : Fin 2 → ℝ := Fin.snoc half_8_01_φ1 (713517265969/10000000000000 : ℝ)

private def half_8_01_φ3 : Fin 3 → ℝ := Fin.snoc half_8_01_φ2 (476504240631/10000000000000 : ℝ)

private theorem half_8_01_hF2 : SourcePowerBound (paddedMoment 9 0 2 8 half_8_01_φ3) (7501601967901/1250000000000 : ℝ) := by
  have h := padded_fourth_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_01_φ3 (by norm_num [half_8_01_φ1, half_8_01_φ2, half_8_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_01_φ1, half_8_01_φ2, half_8_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_01_φ1, half_8_01_φ2, half_8_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_01_φ1, half_8_01_φ2, half_8_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_01_hF1 : SourcePowerBound (paddedMoment 9 0 1 8 half_8_01_φ3) (2917200655967/1250000000000 : ℝ) := by
  have h := padded_second_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_01_φ3 (by norm_num [half_8_01_φ1, half_8_01_φ2, half_8_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_01_φ1, half_8_01_φ2, half_8_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_01_φ1, half_8_01_φ2, half_8_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_01_φ1, half_8_01_φ2, half_8_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_01_hx3 : SourcePowerBound (powerBoxCross 9 5 8 half_8_01_φ3) (60535040390803/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 9) (s := 5) (r := 1) (v := 2) (t := 7) (D := 8)
    (a := (1/14 : ℝ)) (b := (3/14 : ℝ)) (c := (5/7 : ℝ))
    (by norm_num) half_8_01_φ3 (by norm_num [half_8_01_φ1, half_8_01_φ2, half_8_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_01_φ1, half_8_01_φ2, half_8_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_8_01_hF1 half_8_01_hF2 SeedCompletionNinthSecondSeeds.ninth_half_7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_8_01_φ1, half_8_01_φ2, half_8_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_01_hx2 : SourcePowerBound (powerBoxCross 9 6 4 half_8_01_φ2) (70130666699089/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 6) (u := 4) (t := 7)
    (D := 4) (ψ := (476504240631/10000000000000 : ℝ)) half_8_01_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_01_φ1, half_8_01_φ2, half_8_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_01_φ1, half_8_01_φ2, half_8_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_01_φ1, half_8_01_φ2, half_8_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_5 SeedCompletionNinthSecondSeeds.ninth_half_7
    (by simpa only [half_8_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_8_01_hx3)
  exact h.weaken (by norm_num [half_8_01_φ1, half_8_01_φ2, half_8_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_01_hx1 : SourcePowerBound (powerBoxCross 9 7 2 half_8_01_φ1) (8498580923671/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 7) (u := 5) (t := 8)
    (D := 2) (ψ := (713517265969/10000000000000 : ℝ)) half_8_01_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_01_φ1, half_8_01_φ2, half_8_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_01_φ1, half_8_01_φ2, half_8_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_01_φ1, half_8_01_φ2, half_8_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_6 half_8_00
    (by simpa only [half_8_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_8_01_hx2)
  exact h.weaken (by norm_num [half_8_01_φ1, half_8_01_φ2, half_8_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_01 : AdmissibleExponent 9 16 (96591921123339/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 6) (ψ := (892777837433/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_7
    (by simpa only [half_8_01_φ1] using half_8_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_8_01_φ1, half_8_01_φ2, half_8_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (48478269161/500000000000 : ℝ)

private def half_9_01_φ2 : Fin 2 → ℝ := Fin.snoc half_9_01_φ1 (102101973761/1250000000000 : ℝ)

private def half_9_01_φ3 : Fin 3 → ℝ := Fin.snoc half_9_01_φ2 (87088622847/1250000000000 : ℝ)

private theorem half_9_01_hF2 : SourcePowerBound (paddedMoment 9 0 2 8 half_9_01_φ3) (1575182382937/312500000000 : ℝ) := by
  have h := padded_fourth_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_01_φ3 (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_01_hx3 : SourcePowerBound (powerBoxCross 9 6 8 half_9_01_φ3) (13411383253721/2000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 6) (r := 2) (v := 8) (w := 8) (D := 8)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_9_01_φ3 (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_01_hF2 half_8_01 half_8_01
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_01_hx2 : SourcePowerBound (powerBoxCross 9 7 4 half_9_01_φ2) (7988329393859/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (87088622847/1250000000000 : ℝ)) half_9_01_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_6 half_8_01
    (by simpa only [half_9_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_01_hx3)
  exact h.weaken (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_01_hx1 : SourcePowerBound (powerBoxCross 9 8 2 half_9_01_φ1) (3927850728183/400000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (102101973761/1250000000000 : ℝ)) half_9_01_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_7 half_9_00
    (by simpa only [half_9_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_01_hx2)
  exact h.weaken (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_01 : AdmissibleExponent 9 18 (901917991623/80000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 7) (ψ := (48478269161/500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_8_01
    (by simpa only [half_9_01_φ1] using half_9_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_8_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (827156221691/10000000000000 : ℝ)

private def half_8_02_φ2 : Fin 2 → ℝ := Fin.snoc half_8_02_φ1 (44316918023/625000000000 : ℝ)

private def half_8_02_φ3 : Fin 3 → ℝ := Fin.snoc half_8_02_φ2 (457825440261/10000000000000 : ℝ)

private theorem half_8_02_hF2 : SourcePowerBound (paddedMoment 9 0 2 8 half_8_02_φ3) (97098036863/15625000000 : ℝ) := by
  have h := padded_fourth_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_02_φ3 (by norm_num [half_8_02_φ1, half_8_02_φ2, half_8_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_02_φ1, half_8_02_φ2, half_8_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_02_φ1, half_8_02_φ2, half_8_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_02_φ1, half_8_02_φ2, half_8_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_02_hF1 : SourcePowerBound (paddedMoment 9 0 1 8 half_8_02_φ3) (37574345621/15625000000 : ℝ) := by
  have h := padded_second_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_02_φ3 (by norm_num [half_8_02_φ1, half_8_02_φ2, half_8_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_02_φ1, half_8_02_φ2, half_8_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_02_φ1, half_8_02_φ2, half_8_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_02_φ1, half_8_02_φ2, half_8_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_02_hx3 : SourcePowerBound (powerBoxCross 9 5 8 half_8_02_φ3) (15389472429687/2500000000000 : ℝ) := by
  have h := full_B_cross_power (k := 9) (s := 5) (r := 1) (v := 2) (t := 7) (D := 8)
    (a := (1/14 : ℝ)) (b := (3/14 : ℝ)) (c := (5/7 : ℝ))
    (by norm_num) half_8_02_φ3 (by norm_num [half_8_02_φ1, half_8_02_φ2, half_8_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_02_φ1, half_8_02_φ2, half_8_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_8_02_hF1 half_8_02_hF2 SeedCompletionNinthSecondSeeds.ninth_half_7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_8_02_φ1, half_8_02_φ2, half_8_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_02_hx2 : SourcePowerBound (powerBoxCross 9 6 4 half_8_02_φ2) (14224666828507/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 6) (u := 4) (t := 7)
    (D := 4) (ψ := (457825440261/10000000000000 : ℝ)) half_8_02_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_02_φ1, half_8_02_φ2, half_8_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_02_φ1, half_8_02_φ2, half_8_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_02_φ1, half_8_02_φ2, half_8_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_5 SeedCompletionNinthSecondSeeds.ninth_half_7
    (by simpa only [half_8_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_8_02_hx3)
  exact h.weaken (by norm_num [half_8_02_φ1, half_8_02_φ2, half_8_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_02_hx1 : SourcePowerBound (powerBoxCross 9 7 2 half_8_02_φ1) (17090812221217/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 7) (u := 5) (t := 8)
    (D := 2) (ψ := (44316918023/625000000000 : ℝ)) half_8_02_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_02_φ1, half_8_02_φ2, half_8_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_02_φ1, half_8_02_φ2, half_8_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_02_φ1, half_8_02_φ2, half_8_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_6 half_8_01
    (by simpa only [half_8_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_8_02_hx2)
  exact h.weaken (by norm_num [half_8_02_φ1, half_8_02_φ2, half_8_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_02 : AdmissibleExponent 9 16 (24051772997017/2500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 6) (ψ := (827156221691/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_7
    (by simpa only [half_8_02_φ1] using half_8_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_8_02_φ1, half_8_02_φ2, half_8_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (448191421827/5000000000000 : ℝ)

private def half_9_02_φ2 : Fin 2 → ℝ := Fin.snoc half_9_02_φ1 (392518526447/5000000000000 : ℝ)

private def half_9_02_φ3 : Fin 3 → ℝ := Fin.snoc half_9_02_φ2 (646317683389/10000000000000 : ℝ)

private theorem half_9_02_hF2 : SourcePowerBound (paddedMoment 9 0 2 8 half_9_02_φ3) (6766787260189/1250000000000 : ℝ) := by
  have h := padded_fourth_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_02_φ3 (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_02_hx3 : SourcePowerBound (powerBoxCross 9 6 8 half_9_02_φ3) (8611628593831/1250000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 6) (r := 2) (v := 8) (w := 8) (D := 8)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_9_02_φ3 (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_02_hF2 half_8_02 half_8_02
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_02_hx2 : SourcePowerBound (powerBoxCross 9 7 4 half_9_02_φ2) (40645451054459/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (646317683389/10000000000000 : ℝ)) half_9_02_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_6 half_8_02
    (by simpa only [half_9_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_02_hx3)
  exact h.weaken (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_02_hx1 : SourcePowerBound (powerBoxCross 9 8 2 half_9_02_φ1) (98479636162131/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (392518526447/5000000000000 : ℝ)) half_9_02_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_7 half_9_01
    (by simpa only [half_9_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_02_hx2)
  exact h.weaken (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_02 : AdmissibleExponent 9 18 (111925378816941/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 7) (ψ := (448191421827/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_8_02
    (by simpa only [half_9_02_φ1] using half_9_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_8_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (807247951441/10000000000000 : ℝ)

private def half_8_03_φ2 : Fin 2 → ℝ := Fin.snoc half_8_03_φ1 (176930421677/2500000000000 : ℝ)

private def half_8_03_φ3 : Fin 3 → ℝ := Fin.snoc half_8_03_φ2 (452158670227/10000000000000 : ℝ)

private theorem half_8_03_hF2 : SourcePowerBound (paddedMoment 9 0 2 8 half_8_03_φ3) (981076884359/156250000000 : ℝ) := by
  have h := padded_fourth_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_03_φ3 (by norm_num [half_8_03_φ1, half_8_03_φ2, half_8_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_03_φ1, half_8_03_φ2, half_8_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_03_φ1, half_8_03_φ2, half_8_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_03_φ1, half_8_03_φ2, half_8_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_03_hF1 : SourcePowerBound (paddedMoment 9 0 1 8 half_8_03_φ3) (379108961453/156250000000 : ℝ) := by
  have h := padded_second_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_03_φ3 (by norm_num [half_8_03_φ1, half_8_03_φ2, half_8_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_03_φ1, half_8_03_φ2, half_8_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_03_φ1, half_8_03_φ2, half_8_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_03_φ1, half_8_03_φ2, half_8_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_03_hx3 : SourcePowerBound (powerBoxCross 9 5 8 half_8_03_φ3) (30934100752863/5000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 9) (s := 5) (r := 1) (v := 2) (t := 7) (D := 8)
    (a := (1/14 : ℝ)) (b := (3/14 : ℝ)) (c := (5/7 : ℝ))
    (by norm_num) half_8_03_φ3 (by norm_num [half_8_03_φ1, half_8_03_φ2, half_8_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_03_φ1, half_8_03_φ2, half_8_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_8_03_hF1 half_8_03_hF2 SeedCompletionNinthSecondSeeds.ninth_half_7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_8_03_φ1, half_8_03_φ2, half_8_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_03_hx2 : SourcePowerBound (powerBoxCross 9 6 4 half_8_03_φ2) (279001911549/39062500000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 6) (u := 4) (t := 7)
    (D := 4) (ψ := (452158670227/10000000000000 : ℝ)) half_8_03_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_03_φ1, half_8_03_φ2, half_8_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_03_φ1, half_8_03_φ2, half_8_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_03_φ1, half_8_03_φ2, half_8_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_5 SeedCompletionNinthSecondSeeds.ninth_half_7
    (by simpa only [half_8_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_8_03_hx3)
  exact h.weaken (by norm_num [half_8_03_φ1, half_8_03_φ2, half_8_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_03_hx1 : SourcePowerBound (powerBoxCross 9 7 2 half_8_03_φ1) (85596119247363/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 7) (u := 5) (t := 8)
    (D := 2) (ψ := (176930421677/2500000000000 : ℝ)) half_8_03_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_03_φ1, half_8_03_φ2, half_8_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_03_φ1, half_8_03_φ2, half_8_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_03_φ1, half_8_03_φ2, half_8_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_6 half_8_02
    (by simpa only [half_8_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_8_03_hx2)
  exact h.weaken (by norm_num [half_8_03_φ1, half_8_03_φ2, half_8_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_03 : AdmissibleExponent 9 16 (3002823206753/312500000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 6) (ψ := (807247951441/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_7
    (by simpa only [half_8_03_φ1] using half_8_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_8_03_φ1, half_8_03_φ2, half_8_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (431904588549/5000000000000 : ℝ)

private def half_9_03_φ2 : Fin 2 → ℝ := Fin.snoc half_9_03_φ1 (774616588803/10000000000000 : ℝ)

private def half_9_03_φ3 : Fin 3 → ℝ := Fin.snoc half_9_03_φ2 (157126472279/2500000000000 : ℝ)

private theorem half_9_03_hF2 : SourcePowerBound (paddedMoment 9 0 2 8 half_9_03_φ3) (6949205034949/1250000000000 : ℝ) := by
  have h := padded_fourth_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_03_φ3 (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_03_hx3 : SourcePowerBound (powerBoxCross 9 6 8 half_9_03_φ3) (69628899075631/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 6) (r := 2) (v := 8) (w := 8) (D := 8)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_9_03_φ3 (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_03_hF2 half_8_03 half_8_03
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_03_hx2 : SourcePowerBound (powerBoxCross 9 7 4 half_9_03_φ2) (3275634220503/400000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (157126472279/2500000000000 : ℝ)) half_9_03_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_6 half_8_03
    (by simpa only [half_9_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_03_hx3)
  exact h.weaken (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_03_hx1 : SourcePowerBound (powerBoxCross 9 8 2 half_9_03_φ1) (49326889907487/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (774616588803/10000000000000 : ℝ)) half_9_03_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_7 half_9_02
    (by simpa only [half_9_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_03_hx2)
  exact h.weaken (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_03 : AdmissibleExponent 9 18 (27902729367861/2500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 7) (ψ := (431904588549/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_8_03
    (by simpa only [half_9_03_φ1] using half_9_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_8_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (200297772161/2500000000000 : ℝ)

private def half_8_04_φ2 : Fin 2 → ℝ := Fin.snoc half_8_04_φ1 (707311268431/10000000000000 : ℝ)

private def half_8_04_φ3 : Fin 3 → ℝ := Fin.snoc half_8_04_φ2 (28152163779/625000000000 : ℝ)

private theorem half_8_04_hF2 : SourcePowerBound (paddedMoment 9 0 2 8 half_8_04_φ3) (7873189067383/1250000000000 : ℝ) := by
  have h := padded_fourth_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_04_φ3 (by norm_num [half_8_04_φ1, half_8_04_φ2, half_8_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_04_φ1, half_8_04_φ2, half_8_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_04_φ1, half_8_04_φ2, half_8_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_04_φ1, half_8_04_φ2, half_8_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_04_hF1 : SourcePowerBound (paddedMoment 9 0 1 8 half_8_04_φ3) (3041063022461/1250000000000 : ℝ) := by
  have h := padded_second_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_04_φ3 (by norm_num [half_8_04_φ1, half_8_04_φ2, half_8_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_04_φ1, half_8_04_φ2, half_8_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_04_φ1, half_8_04_φ2, half_8_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_04_φ1, half_8_04_φ2, half_8_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_04_hx3 : SourcePowerBound (powerBoxCross 9 5 8 half_8_04_φ3) (61962610306419/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 9) (s := 5) (r := 1) (v := 2) (t := 7) (D := 8)
    (a := (1/14 : ℝ)) (b := (3/14 : ℝ)) (c := (5/7 : ℝ))
    (by norm_num) half_8_04_φ3 (by norm_num [half_8_04_φ1, half_8_04_φ2, half_8_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_04_φ1, half_8_04_φ2, half_8_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_8_04_hF1 half_8_04_hF2 SeedCompletionNinthSecondSeeds.ninth_half_7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_8_04_φ1, half_8_04_φ2, half_8_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_04_hx2 : SourcePowerBound (powerBoxCross 9 6 4 half_8_04_φ2) (71516112374971/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 6) (u := 4) (t := 7)
    (D := 4) (ψ := (28152163779/625000000000 : ℝ)) half_8_04_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_04_φ1, half_8_04_φ2, half_8_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_04_φ1, half_8_04_φ2, half_8_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_04_φ1, half_8_04_φ2, half_8_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_5 SeedCompletionNinthSecondSeeds.ninth_half_7
    (by simpa only [half_8_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_8_04_hx3)
  exact h.weaken (by norm_num [half_8_04_φ1, half_8_04_φ2, half_8_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_04_hx1 : SourcePowerBound (powerBoxCross 9 7 2 half_8_04_φ1) (8563933880689/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 7) (u := 5) (t := 8)
    (D := 2) (ψ := (707311268431/10000000000000 : ℝ)) half_8_04_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_04_φ1, half_8_04_φ2, half_8_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_04_φ1, half_8_04_φ2, half_8_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_04_φ1, half_8_04_φ2, half_8_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_6 half_8_03
    (by simpa only [half_8_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_8_04_hx2)
  exact h.weaken (by norm_num [half_8_04_φ1, half_8_04_φ2, half_8_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_04 : AdmissibleExponent 9 16 (48027411479631/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 6) (ψ := (200297772161/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_7
    (by simpa only [half_8_04_φ1] using half_8_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_8_04_φ1, half_8_04_φ2, half_8_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (53150669471/625000000000 : ℝ)

private def half_9_04_φ2 : Fin 2 → ℝ := Fin.snoc half_9_04_φ1 (385609351657/5000000000000 : ℝ)

private def half_9_04_φ3 : Fin 3 → ℝ := Fin.snoc half_9_04_φ2 (622294956573/10000000000000 : ℝ)

private theorem half_9_04_hF2 : SourcePowerBound (paddedMoment 9 0 2 8 half_9_04_φ3) (7018226885731/1250000000000 : ℝ) := by
  have h := padded_fourth_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_04_φ3 (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_04_hx3 : SourcePowerBound (powerBoxCross 9 6 8 half_9_04_φ3) (69912089123583/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 6) (r := 2) (v := 8) (w := 8) (D := 8)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_9_04_φ3 (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_04_hF2 half_8_04 half_8_04
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_04_hx2 : SourcePowerBound (powerBoxCross 9 7 4 half_9_04_φ2) (82131294325727/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (622294956573/10000000000000 : ℝ)) half_9_04_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_6 half_8_04
    (by simpa only [half_9_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_04_hx3)
  exact h.weaken (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_04_hx1 : SourcePowerBound (powerBoxCross 9 8 2 half_9_04_φ1) (98736628636879/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (385609351657/5000000000000 : ℝ)) half_9_04_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_7 half_9_03
    (by simpa only [half_9_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_04_hx2)
  exact h.weaken (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_04 : AdmissibleExponent 9 18 (111492789309919/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 7) (ψ := (53150669471/625000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_8_04
    (by simpa only [half_9_04_φ1] using half_9_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_8_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (799346773807/10000000000000 : ℝ)

private def half_8_05_φ2 : Fin 2 → ℝ := Fin.snoc half_8_05_φ1 (353593148029/5000000000000 : ℝ)

private def half_8_05_φ3 : Fin 3 → ℝ := Fin.snoc half_8_05_φ2 (224954823639/5000000000000 : ℝ)

private theorem half_8_05_hF2 : SourcePowerBound (paddedMoment 9 0 2 8 half_8_05_φ3) (7880671848571/1250000000000 : ℝ) := by
  have h := padded_fourth_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_05_φ3 (by norm_num [half_8_05_φ1, half_8_05_φ2, half_8_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_05_φ1, half_8_05_φ2, half_8_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_05_φ1, half_8_05_φ2, half_8_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_05_φ1, half_8_05_φ2, half_8_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_05_hF1 : SourcePowerBound (paddedMoment 9 0 1 8 half_8_05_φ3) (3043557282857/1250000000000 : ℝ) := by
  have h := padded_second_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_05_φ3 (by norm_num [half_8_05_φ1, half_8_05_φ2, half_8_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_05_φ1, half_8_05_φ2, half_8_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_05_φ1, half_8_05_φ2, half_8_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_05_φ1, half_8_05_φ2, half_8_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_05_hx3 : SourcePowerBound (powerBoxCross 9 5 8 half_8_05_φ3) (6199135778803/1000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 9) (s := 5) (r := 1) (v := 2) (t := 7) (D := 8)
    (a := (1/14 : ℝ)) (b := (3/14 : ℝ)) (c := (5/7 : ℝ))
    (by norm_num) half_8_05_φ3 (by norm_num [half_8_05_φ1, half_8_05_φ2, half_8_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_05_φ1, half_8_05_φ2, half_8_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_8_05_hF1 half_8_05_hF2 SeedCompletionNinthSecondSeeds.ninth_half_7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_8_05_φ1, half_8_05_φ2, half_8_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_05_hx2 : SourcePowerBound (powerBoxCross 9 6 4 half_8_05_φ2) (2235750362057/312500000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 6) (u := 4) (t := 7)
    (D := 4) (ψ := (224954823639/5000000000000 : ℝ)) half_8_05_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_05_φ1, half_8_05_φ2, half_8_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_05_φ1, half_8_05_φ2, half_8_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_05_φ1, half_8_05_φ2, half_8_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_5 SeedCompletionNinthSecondSeeds.ninth_half_7
    (by simpa only [half_8_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_8_05_hx3)
  exact h.weaken (by norm_num [half_8_05_φ1, half_8_05_φ2, half_8_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_05_hx1 : SourcePowerBound (powerBoxCross 9 7 2 half_8_05_φ1) (4282624958179/500000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 7) (u := 5) (t := 8)
    (D := 2) (ψ := (353593148029/5000000000000 : ℝ)) half_8_05_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_05_φ1, half_8_05_φ2, half_8_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_05_φ1, half_8_05_φ2, half_8_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_05_φ1, half_8_05_φ2, half_8_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_6 half_8_04
    (by simpa only [half_8_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_8_05_hx2)
  exact h.weaken (by norm_num [half_8_05_φ1, half_8_05_φ2, half_8_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_05 : AdmissibleExponent 9 16 (96044007223071/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 6) (ψ := (799346773807/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_7
    (by simpa only [half_8_05_φ1] using half_8_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_8_05_φ1, half_8_05_φ2, half_8_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (211291859151/2500000000000 : ℝ)

private def half_9_05_φ2 : Fin 2 → ℝ := Fin.snoc half_9_05_φ1 (770112442473/10000000000000 : ℝ)

private def half_9_05_φ3 : Fin 3 → ℝ := Fin.snoc half_9_05_φ2 (620146506579/10000000000000 : ℝ)

private theorem half_9_05_hF2 : SourcePowerBound (paddedMoment 9 0 2 8 half_9_05_φ3) (880465105379/156250000000 : ℝ) := by
  have h := padded_fourth_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_05_φ3 (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_05_hx3 : SourcePowerBound (powerBoxCross 9 6 8 half_9_05_φ3) (35008999504287/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 6) (r := 2) (v := 8) (w := 8) (D := 8)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_9_05_φ3 (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_05_hF2 half_8_05 half_8_05
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_05_hx2 : SourcePowerBound (powerBoxCross 9 7 4 half_9_05_φ2) (10277973970879/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (620146506579/10000000000000 : ℝ)) half_9_05_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_6 half_8_05
    (by simpa only [half_9_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_05_hx3)
  exact h.weaken (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_05_hx1 : SourcePowerBound (powerBoxCross 9 8 2 half_9_05_φ1) (9877184792109/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (770112442473/10000000000000 : ℝ)) half_9_05_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_7 half_9_04
    (by simpa only [half_9_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_05_hx2)
  exact h.weaken (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_05 : AdmissibleExponent 9 18 (2228987189403/200000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 7) (ψ := (211291859151/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_8_05
    (by simpa only [half_9_05_φ1] using half_9_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_8_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (199696258253/2500000000000 : ℝ)

private def half_8_06_φ2 : Fin 2 → ℝ := Fin.snoc half_8_06_φ1 (353574116007/5000000000000 : ℝ)

private def half_8_06_φ3 : Fin 3 → ℝ := Fin.snoc half_8_06_φ2 (449749751121/10000000000000 : ℝ)

private theorem half_8_06_hF2 : SourcePowerBound (paddedMoment 9 0 2 8 half_8_06_φ3) (7882950951559/1250000000000 : ℝ) := by
  have h := padded_fourth_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_06_φ3 (by norm_num [half_8_06_φ1, half_8_06_φ2, half_8_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_06_φ1, half_8_06_φ2, half_8_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_06_φ1, half_8_06_φ2, half_8_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_06_φ1, half_8_06_φ2, half_8_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_06_hF1 : SourcePowerBound (paddedMoment 9 0 1 8 half_8_06_φ3) (3044316983853/1250000000000 : ℝ) := by
  have h := padded_second_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_06_φ3 (by norm_num [half_8_06_φ1, half_8_06_φ2, half_8_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_06_φ1, half_8_06_φ2, half_8_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_06_φ1, half_8_06_φ2, half_8_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_06_φ1, half_8_06_φ2, half_8_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_06_hx3 : SourcePowerBound (powerBoxCross 9 5 8 half_8_06_φ3) (1240002273727/200000000000 : ℝ) := by
  have h := full_B_cross_power (k := 9) (s := 5) (r := 1) (v := 2) (t := 7) (D := 8)
    (a := (1/14 : ℝ)) (b := (3/14 : ℝ)) (c := (5/7 : ℝ))
    (by norm_num) half_8_06_φ3 (by norm_num [half_8_06_φ1, half_8_06_φ2, half_8_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_06_φ1, half_8_06_φ2, half_8_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_8_06_hF1 half_8_06_hF2 SeedCompletionNinthSecondSeeds.ninth_half_7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_8_06_φ1, half_8_06_φ2, half_8_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_06_hx2 : SourcePowerBound (powerBoxCross 9 6 4 half_8_06_φ2) (71552509118123/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 6) (u := 4) (t := 7)
    (D := 4) (ψ := (449749751121/10000000000000 : ℝ)) half_8_06_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_06_φ1, half_8_06_φ2, half_8_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_06_φ1, half_8_06_φ2, half_8_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_06_φ1, half_8_06_φ2, half_8_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_5 SeedCompletionNinthSecondSeeds.ninth_half_7
    (by simpa only [half_8_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_8_06_hx3)
  exact h.weaken (by norm_num [half_8_06_φ1, half_8_06_φ2, half_8_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_06_hx1 : SourcePowerBound (powerBoxCross 9 7 2 half_8_06_φ1) (21414126885153/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 7) (u := 5) (t := 8)
    (D := 2) (ψ := (353574116007/5000000000000 : ℝ)) half_8_06_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_06_φ1, half_8_06_φ2, half_8_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_06_φ1, half_8_06_φ2, half_8_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_06_φ1, half_8_06_φ2, half_8_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_6 half_8_05
    (by simpa only [half_8_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_8_06_hx2)
  exact h.weaken (by norm_num [half_8_06_φ1, half_8_06_φ2, half_8_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_06 : AdmissibleExponent 9 16 (12005089121221/1250000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 6) (ψ := (199696258253/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_7
    (by simpa only [half_8_06_φ1] using half_8_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_8_06_φ1, half_8_06_φ2, half_8_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (26349509607/312500000000 : ℝ)

private def half_9_06_φ2 : Fin 2 → ℝ := Fin.snoc half_9_06_φ1 (384876121997/5000000000000 : ℝ)

private def half_9_06_φ3 : Fin 3 → ℝ := Fin.snoc half_9_06_φ2 (619407567651/10000000000000 : ℝ)

private theorem half_9_06_hF2 : SourcePowerBound (paddedMoment 9 0 2 8 half_9_06_φ3) (7052967642793/1250000000000 : ℝ) := by
  have h := padded_fourth_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_06_φ3 (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_06_hx3 : SourcePowerBound (powerBoxCross 9 6 8 half_9_06_φ3) (35028387976859/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 6) (r := 2) (v := 8) (w := 8) (D := 8)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_9_06_φ3 (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_06_hF2 half_8_06 half_8_06
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_06_hx2 : SourcePowerBound (powerBoxCross 9 7 4 half_9_06_φ2) (82258361059493/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (619407567651/10000000000000 : ℝ)) half_9_06_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_6 half_8_06
    (by simpa only [half_9_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_06_hx3)
  exact h.weaken (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_06_hx1 : SourcePowerBound (powerBoxCross 9 8 2 half_9_06_φ1) (98785895072203/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (384876121997/5000000000000 : ℝ)) half_9_06_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_7 half_9_05
    (by simpa only [half_9_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_06_hx2)
  exact h.weaken (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_06 : AdmissibleExponent 9 18 (111433659683563/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 7) (ψ := (26349509607/312500000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_8_06
    (by simpa only [half_9_06_φ1] using half_9_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_8_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (798613924561/10000000000000 : ℝ)

private def half_8_07_φ2 : Fin 2 → ℝ := Fin.snoc half_8_07_φ1 (707136637557/10000000000000 : ℝ)

private def half_8_07_φ3 : Fin 3 → ℝ := Fin.snoc half_8_07_φ2 (112425261531/2500000000000 : ℝ)

private theorem half_8_07_hF2 : SourcePowerBound (paddedMoment 9 0 2 8 half_8_07_φ3) (3941822587637/625000000000 : ℝ) := by
  have h := padded_fourth_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_07_φ3 (by norm_num [half_8_07_φ1, half_8_07_φ2, half_8_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_07_φ1, half_8_07_φ2, half_8_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_07_φ1, half_8_07_φ2, half_8_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_07_φ1, half_8_07_φ2, half_8_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_07_hF1 : SourcePowerBound (paddedMoment 9 0 1 8 half_8_07_φ3) (1522274195879/625000000000 : ℝ) := by
  have h := padded_second_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_07_φ3 (by norm_num [half_8_07_φ1, half_8_07_φ2, half_8_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_07_φ1, half_8_07_φ2, half_8_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_07_φ1, half_8_07_φ2, half_8_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_07_φ1, half_8_07_φ2, half_8_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_07_hx3 : SourcePowerBound (powerBoxCross 9 5 8 half_8_07_φ3) (62002780767343/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 9) (s := 5) (r := 1) (v := 2) (t := 7) (D := 8)
    (a := (1/14 : ℝ)) (b := (3/14 : ℝ)) (c := (5/7 : ℝ))
    (by norm_num) half_8_07_φ3 (by norm_num [half_8_07_φ1, half_8_07_φ2, half_8_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_07_φ1, half_8_07_φ2, half_8_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_8_07_hF1 half_8_07_hF2 SeedCompletionNinthSecondSeeds.ninth_half_7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_8_07_φ1, half_8_07_φ2, half_8_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_07_hx2 : SourcePowerBound (powerBoxCross 9 6 4 half_8_07_φ2) (17888774374953/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 6) (u := 4) (t := 7)
    (D := 4) (ψ := (112425261531/2500000000000 : ℝ)) half_8_07_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_07_φ1, half_8_07_φ2, half_8_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_07_φ1, half_8_07_φ2, half_8_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_07_φ1, half_8_07_φ2, half_8_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_5 SeedCompletionNinthSecondSeeds.ninth_half_7
    (by simpa only [half_8_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_8_07_hx3)
  exact h.weaken (by norm_num [half_8_07_φ1, half_8_07_φ2, half_8_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_07_hx1 : SourcePowerBound (powerBoxCross 9 7 2 half_8_07_φ1) (85657728507989/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 7) (u := 5) (t := 8)
    (D := 2) (ψ := (707136637557/10000000000000 : ℝ)) half_8_07_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_07_φ1, half_8_07_φ2, half_8_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_07_φ1, half_8_07_φ2, half_8_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_07_φ1, half_8_07_φ2, half_8_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_6 half_8_06
    (by simpa only [half_8_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_8_07_hx2)
  exact h.weaken (by norm_num [half_8_07_φ1, half_8_07_φ2, half_8_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_07 : AdmissibleExponent 9 16 (48019854763641/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 6) (ψ := (798613924561/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_7
    (by simpa only [half_8_07_φ1] using half_8_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_8_07_φ1, half_8_07_φ2, half_8_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (52653274209/625000000000 : ℝ)

private def half_9_07_φ2 : Fin 2 → ℝ := Fin.snoc half_9_07_φ1 (96204360689/1250000000000 : ℝ)

private def half_9_07_φ3 : Fin 3 → ℝ := Fin.snoc half_9_07_φ2 (154788643881/2500000000000 : ℝ)

private theorem half_9_07_hF2 : SourcePowerBound (paddedMoment 9 0 2 8 half_9_07_φ3) (352813722743/62500000000 : ℝ) := by
  have h := padded_fourth_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_07_φ3 (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_07_hx3 : SourcePowerBound (powerBoxCross 9 6 8 half_9_07_φ3) (70070744629917/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 6) (r := 2) (v := 8) (w := 8) (D := 8)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_9_07_φ3 (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_07_hF2 half_8_07 half_8_07
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_07_hx2 : SourcePowerBound (powerBoxCross 9 7 4 half_9_07_φ2) (82271008481673/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (154788643881/2500000000000 : ℝ)) half_9_07_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_6 half_8_07
    (by simpa only [half_9_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_07_hx3)
  exact h.weaken (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_07_hx1 : SourcePowerBound (powerBoxCross 9 8 2 half_9_07_φ1) (49395636828763/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (96204360689/1250000000000 : ℝ)) half_9_07_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_7 half_9_06
    (by simpa only [half_9_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_07_hx2)
  exact h.weaken (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_07 : AdmissibleExponent 9 18 (55714029733843/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 7) (ψ := (52653274209/625000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_8_07
    (by simpa only [half_9_07_φ1] using half_9_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_8_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (79856180299/1000000000000 : ℝ)

private def half_8_08_φ2 : Fin 2 → ℝ := Fin.snoc half_8_08_φ1 (353566552877/5000000000000 : ℝ)

private def half_8_08_φ3 : Fin 3 → ℝ := Fin.snoc half_8_08_φ2 (449686210031/10000000000000 : ℝ)

private theorem half_8_08_hF2 : SourcePowerBound (paddedMoment 9 0 2 8 half_8_08_φ3) (315354265747/50000000000 : ℝ) := by
  have h := padded_fourth_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_08_φ3 (by norm_num [half_8_08_φ1, half_8_08_φ2, half_8_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_08_φ1, half_8_08_φ2, half_8_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_08_φ1, half_8_08_φ2, half_8_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_08_φ1, half_8_08_φ2, half_8_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_08_hF1 : SourcePowerBound (paddedMoment 9 0 1 8 half_8_08_φ3) (121784755249/50000000000 : ℝ) := by
  have h := padded_second_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_08_φ3 (by norm_num [half_8_08_φ1, half_8_08_φ2, half_8_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_08_φ1, half_8_08_φ2, half_8_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_08_φ1, half_8_08_φ2, half_8_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_08_φ1, half_8_08_φ2, half_8_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_08_hx3 : SourcePowerBound (powerBoxCross 9 5 8 half_8_08_φ3) (62003593190401/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 9) (s := 5) (r := 1) (v := 2) (t := 7) (D := 8)
    (a := (1/14 : ℝ)) (b := (3/14 : ℝ)) (c := (5/7 : ℝ))
    (by norm_num) half_8_08_φ3 (by norm_num [half_8_08_φ1, half_8_08_φ2, half_8_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_08_φ1, half_8_08_φ2, half_8_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_8_08_hF1 half_8_08_hF2 SeedCompletionNinthSecondSeeds.ninth_half_7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_8_08_φ1, half_8_08_φ2, half_8_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_08_hx2 : SourcePowerBound (powerBoxCross 9 6 4 half_8_08_φ2) (2862235438007/400000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 6) (u := 4) (t := 7)
    (D := 4) (ψ := (449686210031/10000000000000 : ℝ)) half_8_08_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_08_φ1, half_8_08_φ2, half_8_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_08_φ1, half_8_08_φ2, half_8_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_08_φ1, half_8_08_φ2, half_8_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_5 SeedCompletionNinthSecondSeeds.ninth_half_7
    (by simpa only [half_8_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_8_08_hx3)
  exact h.weaken (by norm_num [half_8_08_φ1, half_8_08_φ2, half_8_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_08_hx1 : SourcePowerBound (powerBoxCross 9 7 2 half_8_08_φ1) (85658100428479/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 7) (u := 5) (t := 8)
    (D := 2) (ψ := (353566552877/5000000000000 : ℝ)) half_8_08_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_08_φ1, half_8_08_φ2, half_8_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_08_φ1, half_8_08_φ2, half_8_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_08_φ1, half_8_08_φ2, half_8_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_6 half_8_07
    (by simpa only [half_8_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_8_08_hx2)
  exact h.weaken (by norm_num [half_8_08_φ1, half_8_08_φ2, half_8_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_08 : AdmissibleExponent 9 16 (96039403867349/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 6) (ψ := (79856180299/1000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_7
    (by simpa only [half_8_08_φ1] using half_8_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_8_08_φ1, half_8_08_φ2, half_8_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (842187147601/10000000000000 : ℝ)

private def half_9_08_φ2 : Fin 2 → ℝ := Fin.snoc half_9_08_φ1 (769596616181/10000000000000 : ℝ)

private def half_9_08_φ3 : Fin 3 → ℝ := Fin.snoc half_9_08_φ2 (19345884073/312500000000 : ℝ)

private theorem half_9_08_hF2 : SourcePowerBound (paddedMoment 9 0 2 8 half_9_08_φ3) (3528721918823/625000000000 : ℝ) := by
  have h := padded_fourth_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_08_φ3 (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_08_hx3 : SourcePowerBound (powerBoxCross 9 6 8 half_9_08_φ3) (70075712971273/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 6) (r := 2) (v := 8) (w := 8) (D := 8)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_9_08_φ3 (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_08_hF2 half_8_08 half_8_08
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_08_hx2 : SourcePowerBound (powerBoxCross 9 7 4 half_9_08_φ2) (82275561369197/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (19345884073/312500000000 : ℝ)) half_9_08_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_6 half_8_08
    (by simpa only [half_9_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_08_hx3)
  exact h.weaken (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_08_hx1 : SourcePowerBound (powerBoxCross 9 8 2 half_9_08_φ1) (24698318963731/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (769596616181/10000000000000 : ℝ)) half_9_08_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_7 half_9_07
    (by simpa only [half_9_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_08_hx2)
  exact h.weaken (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_08 : AdmissibleExponent 9 18 (111426083068939/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 7) (ψ := (842187147601/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_8_08
    (by simpa only [half_9_08_φ1] using half_9_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_8_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (798545926053/10000000000000 : ℝ)

private def half_8_09_φ2 : Fin 2 → ℝ := Fin.snoc half_8_09_φ1 (707132029919/10000000000000 : ℝ)

private def half_8_09_φ3 : Fin 3 → ℝ := Fin.snoc half_8_09_φ2 (112420422689/2500000000000 : ℝ)

private theorem half_8_09_hF2 : SourcePowerBound (paddedMoment 9 0 2 8 half_8_09_φ3) (985490132477/156250000000 : ℝ) := by
  have h := padded_fourth_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_09_φ3 (by norm_num [half_8_09_φ1, half_8_09_φ2, half_8_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_09_φ1, half_8_09_φ2, half_8_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_09_φ1, half_8_09_φ2, half_8_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_09_φ1, half_8_09_φ2, half_8_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_09_hF1 : SourcePowerBound (paddedMoment 9 0 1 8 half_8_09_φ3) (380580044159/156250000000 : ℝ) := by
  have h := padded_second_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_09_φ3 (by norm_num [half_8_09_φ1, half_8_09_φ2, half_8_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_09_φ1, half_8_09_φ2, half_8_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_09_φ1, half_8_09_φ2, half_8_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_09_φ1, half_8_09_φ2, half_8_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_09_hx3 : SourcePowerBound (powerBoxCross 9 5 8 half_8_09_φ3) (2480153626619/400000000000 : ℝ) := by
  have h := full_B_cross_power (k := 9) (s := 5) (r := 1) (v := 2) (t := 7) (D := 8)
    (a := (1/14 : ℝ)) (b := (3/14 : ℝ)) (c := (5/7 : ℝ))
    (by norm_num) half_8_09_φ3 (by norm_num [half_8_09_φ1, half_8_09_φ2, half_8_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_09_φ1, half_8_09_φ2, half_8_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_8_09_hF1 half_8_09_hF2 SeedCompletionNinthSecondSeeds.ninth_half_7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_8_09_φ1, half_8_09_φ2, half_8_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_09_hx2 : SourcePowerBound (powerBoxCross 9 6 4 half_8_09_φ2) (71556126122841/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 6) (u := 4) (t := 7)
    (D := 4) (ψ := (112420422689/2500000000000 : ℝ)) half_8_09_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_09_φ1, half_8_09_φ2, half_8_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_09_φ1, half_8_09_φ2, half_8_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_09_φ1, half_8_09_φ2, half_8_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_5 SeedCompletionNinthSecondSeeds.ninth_half_7
    (by simpa only [half_8_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_8_09_hx3)
  exact h.weaken (by norm_num [half_8_09_φ1, half_8_09_φ2, half_8_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_09_hx1 : SourcePowerBound (powerBoxCross 9 7 2 half_8_09_φ1) (5353638357531/625000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 7) (u := 5) (t := 8)
    (D := 2) (ψ := (707132029919/10000000000000 : ℝ)) half_8_09_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_09_φ1, half_8_09_φ2, half_8_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_09_φ1, half_8_09_φ2, half_8_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_09_φ1, half_8_09_φ2, half_8_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_6 half_8_08
    (by simpa only [half_8_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_8_09_hx2)
  exact h.weaken (by norm_num [half_8_09_φ1, half_8_09_φ2, half_8_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_09 : AdmissibleExponent 9 16 (19207862151837/2000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 6) (ψ := (798545926053/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_7
    (by simpa only [half_8_09_φ1] using half_8_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_8_09_φ1, half_8_09_φ2, half_8_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (210523092581/2500000000000 : ℝ)

private def half_9_09_φ2 : Fin 2 → ℝ := Fin.snoc half_9_09_φ1 (384792063091/5000000000000 : ℝ)

private def half_9_09_φ3 : Fin 3 → ℝ := Fin.snoc half_9_09_φ2 (38689934947/625000000000 : ℝ)

private theorem half_9_09_hF2 : SourcePowerBound (paddedMoment 9 0 2 8 half_9_09_φ3) (3528926816513/625000000000 : ℝ) := by
  have h := padded_fourth_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_09_φ3 (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_09_hx3 : SourcePowerBound (powerBoxCross 9 6 8 half_9_09_φ3) (70077462220847/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 6) (r := 2) (v := 8) (w := 8) (D := 8)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_9_09_φ3 (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_09_hF2 half_8_09 half_8_09
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_09_hx2 : SourcePowerBound (powerBoxCross 9 7 4 half_9_09_φ2) (1285580934137/156250000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (38689934947/625000000000 : ℝ)) half_9_09_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_6 half_8_09
    (by simpa only [half_9_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_09_hx3)
  exact h.weaken (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_09_hx1 : SourcePowerBound (powerBoxCross 9 8 2 half_9_09_φ1) (98794006045369/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (384792063091/5000000000000 : ℝ)) half_9_09_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_7 half_9_08
    (by simpa only [half_9_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_09_hx2)
  exact h.weaken (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_09 : AdmissibleExponent 9 18 (111425391600229/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 7) (ψ := (210523092581/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_8_09
    (by simpa only [half_9_09_φ1] using half_9_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_8_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (49908818107/625000000000 : ℝ)

private def half_8_10_φ2 : Fin 2 → ℝ := Fin.snoc half_8_10_φ1 (141426340441/2000000000000 : ℝ)

private def half_8_10_φ3 : Fin 3 → ℝ := Fin.snoc half_8_10_φ2 (11242007853/250000000000 : ℝ)

private theorem half_8_10_hF2 : SourcePowerBound (paddedMoment 9 0 2 8 half_8_10_φ3) (7883940681889/1250000000000 : ℝ) := by
  have h := padded_fourth_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_10_φ3 (by norm_num [half_8_10_φ1, half_8_10_φ2, half_8_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_10_φ1, half_8_10_φ2, half_8_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_10_φ1, half_8_10_φ2, half_8_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_10_φ1, half_8_10_φ2, half_8_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_10_hF1 : SourcePowerBound (paddedMoment 9 0 1 8 half_8_10_φ3) (3044646893963/1250000000000 : ℝ) := by
  have h := padded_second_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_10_φ3 (by norm_num [half_8_10_φ1, half_8_10_φ2, half_8_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_10_φ1, half_8_10_φ2, half_8_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_10_φ1, half_8_10_φ2, half_8_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_10_φ1, half_8_10_φ2, half_8_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_10_hx3 : SourcePowerBound (powerBoxCross 9 5 8 half_8_10_φ3) (62003916049903/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 9) (s := 5) (r := 1) (v := 2) (t := 7) (D := 8)
    (a := (1/14 : ℝ)) (b := (3/14 : ℝ)) (c := (5/7 : ℝ))
    (by norm_num) half_8_10_φ3 (by norm_num [half_8_10_φ1, half_8_10_φ2, half_8_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_10_φ1, half_8_10_φ2, half_8_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_8_10_hF1 half_8_10_hF2 SeedCompletionNinthSecondSeeds.ninth_half_7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_8_10_φ1, half_8_10_φ2, half_8_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_10_hx2 : SourcePowerBound (powerBoxCross 9 6 4 half_8_10_φ2) (35778099641423/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 6) (u := 4) (t := 7)
    (D := 4) (ψ := (11242007853/250000000000 : ℝ)) half_8_10_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_10_φ1, half_8_10_φ2, half_8_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_10_φ1, half_8_10_φ2, half_8_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_10_φ1, half_8_10_φ2, half_8_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_5 SeedCompletionNinthSecondSeeds.ninth_half_7
    (by simpa only [half_8_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_8_10_hx3)
  exact h.weaken (by norm_num [half_8_10_φ1, half_8_10_φ2, half_8_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_10_hx1 : SourcePowerBound (powerBoxCross 9 7 2 half_8_10_φ1) (42829124115427/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 7) (u := 5) (t := 8)
    (D := 2) (ψ := (141426340441/2000000000000 : ℝ)) half_8_10_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_10_φ1, half_8_10_φ2, half_8_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_10_φ1, half_8_10_φ2, half_8_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_10_φ1, half_8_10_φ2, half_8_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_6 half_8_09
    (by simpa only [half_8_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_8_10_hx2)
  exact h.weaken (by norm_num [half_8_10_φ1, half_8_10_φ2, half_8_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_10 : AdmissibleExponent 9 16 (9603928239711/1000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 6) (ψ := (49908818107/625000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_7
    (by simpa only [half_8_10_φ1] using half_8_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_8_10_φ1, half_8_10_φ2, half_8_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (421029438953/5000000000000 : ℝ)

private def half_9_10_φ2 : Fin 2 → ℝ := Fin.snoc half_9_10_φ1 (48098752899/625000000000 : ℝ)

private def half_9_10_φ3 : Fin 3 → ℝ := Fin.snoc half_9_10_φ2 (619029017151/10000000000000 : ℝ)

private theorem half_9_10_hF2 : SourcePowerBound (paddedMoment 9 0 2 8 half_9_10_φ3) (7057996175677/1250000000000 : ℝ) := by
  have h := padded_fourth_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_10_φ3 (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_10_hx3 : SourcePowerBound (powerBoxCross 9 6 8 half_9_10_φ3) (3503903651101/500000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 6) (r := 2) (v := 8) (w := 8) (D := 8)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_9_10_φ3 (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_10_hF2 half_8_10 half_8_10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_10_hx2 : SourcePowerBound (powerBoxCross 9 7 4 half_9_10_φ2) (82277749318133/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (619029017151/10000000000000 : ℝ)) half_9_10_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_6 half_8_10
    (by simpa only [half_9_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_10_hx3)
  exact h.weaken (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_10_hx1 : SourcePowerBound (powerBoxCross 9 8 2 half_9_10_φ1) (98794268237997/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (48098752899/625000000000 : ℝ)) half_9_10_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_7 half_9_09
    (by simpa only [half_9_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_10_hx2)
  exact h.weaken (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_10 : AdmissibleExponent 9 18 (111425151406587/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 7) (ψ := (421029438953/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_8_10
    (by simpa only [half_9_10_φ1] using half_9_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_8_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (199634904123/2500000000000 : ℝ)

private def half_8_11_φ2 : Fin 2 → ℝ := Fin.snoc half_8_11_φ1 (353565801189/5000000000000 : ℝ)

private def half_8_11_φ3 : Fin 3 → ℝ := Fin.snoc half_8_11_φ2 (449679894777/10000000000000 : ℝ)

private theorem half_8_11_hF2 : SourcePowerBound (paddedMoment 9 0 2 8 half_8_11_φ3) (7883946659059/1250000000000 : ℝ) := by
  have h := padded_fourth_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_11_φ3 (by norm_num [half_8_11_φ1, half_8_11_φ2, half_8_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_11_φ1, half_8_11_φ2, half_8_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_11_φ1, half_8_11_φ2, half_8_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_11_φ1, half_8_11_φ2, half_8_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_11_hF1 : SourcePowerBound (paddedMoment 9 0 1 8 half_8_11_φ3) (3044648886353/1250000000000 : ℝ) := by
  have h := padded_second_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_11_φ3 (by norm_num [half_8_11_φ1, half_8_11_φ2, half_8_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_11_φ1, half_8_11_φ2, half_8_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_11_φ1, half_8_11_φ2, half_8_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_11_φ1, half_8_11_φ2, half_8_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_11_hx3 : SourcePowerBound (powerBoxCross 9 5 8 half_8_11_φ3) (62003939013101/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 9) (s := 5) (r := 1) (v := 2) (t := 7) (D := 8)
    (a := (1/14 : ℝ)) (b := (3/14 : ℝ)) (c := (5/7 : ℝ))
    (by norm_num) half_8_11_φ3 (by norm_num [half_8_11_φ1, half_8_11_φ2, half_8_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_11_φ1, half_8_11_φ2, half_8_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_8_11_hF1 half_8_11_hF2 SeedCompletionNinthSecondSeeds.ninth_half_7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_8_11_φ1, half_8_11_φ2, half_8_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_11_hx2 : SourcePowerBound (powerBoxCross 9 6 4 half_8_11_φ2) (71556221568457/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 6) (u := 4) (t := 7)
    (D := 4) (ψ := (449679894777/10000000000000 : ℝ)) half_8_11_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_11_φ1, half_8_11_φ2, half_8_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_11_φ1, half_8_11_φ2, half_8_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_11_φ1, half_8_11_φ2, half_8_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_5 SeedCompletionNinthSecondSeeds.ninth_half_7
    (by simpa only [half_8_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_8_11_hx3)
  exact h.weaken (by norm_num [half_8_11_φ1, half_8_11_φ2, half_8_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_11_hx1 : SourcePowerBound (powerBoxCross 9 7 2 half_8_11_φ1) (85658258743217/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 7) (u := 5) (t := 8)
    (D := 2) (ψ := (353565801189/5000000000000 : ℝ)) half_8_11_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_11_φ1, half_8_11_φ2, half_8_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_11_φ1, half_8_11_φ2, half_8_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_11_φ1, half_8_11_φ2, half_8_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_6 half_8_10
    (by simpa only [half_8_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_8_11_hx2)
  exact h.weaken (by norm_num [half_8_11_φ1, half_8_11_φ2, half_8_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_11 : AdmissibleExponent 9 16 (96039273757613/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 6) (ψ := (199634904123/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_7
    (by simpa only [half_8_11_φ1] using half_8_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_8_11_φ1, half_8_11_φ2, half_8_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (168409429573/2000000000000 : ℝ)

private def half_9_11_φ2 : Fin 2 → ℝ := Fin.snoc half_9_11_φ1 (769578712671/10000000000000 : ℝ)

private def half_9_11_φ3 : Fin 3 → ℝ := Fin.snoc half_9_11_φ2 (619025655723/10000000000000 : ℝ)

private theorem half_9_11_hF2 : SourcePowerBound (paddedMoment 9 0 2 8 half_9_11_φ3) (7058045451223/1250000000000 : ℝ) := by
  have h := padded_fourth_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_11_φ3 (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_11_hx3 : SourcePowerBound (powerBoxCross 9 6 8 half_9_11_φ3) (70078284848569/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 6) (r := 2) (v := 8) (w := 8) (D := 8)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_9_11_φ3 (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_11_hF2 half_8_11 half_8_11
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_11_hx2 : SourcePowerBound (powerBoxCross 9 7 4 half_9_11_φ2) (82277948106681/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (619025655723/10000000000000 : ℝ)) half_9_11_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_6 half_8_11
    (by simpa only [half_9_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_11_hx3)
  exact h.weaken (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_11_hx1 : SourcePowerBound (powerBoxCross 9 8 2 half_9_11_φ1) (98794361250419/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (769578712671/10000000000000 : ℝ)) half_9_11_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_7 half_9_10
    (by simpa only [half_9_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_11_hx2)
  exact h.weaken (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_11 : AdmissibleExponent 9 18 (55712534234197/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 7) (ψ := (168409429573/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_8_11
    (by simpa only [half_9_11_φ1] using half_9_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_8_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (49908697983/625000000000 : ℝ)

private def half_8_12_φ2 : Fin 2 → ℝ := Fin.snoc half_8_12_φ1 (707131571969/10000000000000 : ℝ)

private def half_8_12_φ3 : Fin 3 → ℝ := Fin.snoc half_8_12_φ2 (449679767039/10000000000000 : ℝ)

private theorem half_8_12_hF2 : SourcePowerBound (paddedMoment 9 0 2 8 half_8_12_φ3) (492746779987/78125000000 : ℝ) := by
  have h := padded_fourth_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_12_φ3 (by norm_num [half_8_12_φ1, half_8_12_φ2, half_8_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_12_φ1, half_8_12_φ2, half_8_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_12_φ1, half_8_12_φ2, half_8_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_12_φ1, half_8_12_φ2, half_8_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_12_hF1 : SourcePowerBound (paddedMoment 9 0 1 8 half_8_12_φ3) (190290593329/78125000000 : ℝ) := by
  have h := padded_second_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_12_φ3 (by norm_num [half_8_12_φ1, half_8_12_φ2, half_8_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_12_φ1, half_8_12_φ2, half_8_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_12_φ1, half_8_12_φ2, half_8_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_12_φ1, half_8_12_φ2, half_8_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_12_hx3 : SourcePowerBound (powerBoxCross 9 5 8 half_8_12_φ3) (2480157840321/400000000000 : ℝ) := by
  have h := full_B_cross_power (k := 9) (s := 5) (r := 1) (v := 2) (t := 7) (D := 8)
    (a := (1/14 : ℝ)) (b := (3/14 : ℝ)) (c := (5/7 : ℝ))
    (by norm_num) half_8_12_φ3 (by norm_num [half_8_12_φ1, half_8_12_φ2, half_8_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_12_φ1, half_8_12_φ2, half_8_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_8_12_hF1 half_8_12_hF2 SeedCompletionNinthSecondSeeds.ninth_half_7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_8_12_φ1, half_8_12_φ2, half_8_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_12_hx2 : SourcePowerBound (powerBoxCross 9 6 4 half_8_12_φ2) (35778114178489/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 6) (u := 4) (t := 7)
    (D := 4) (ψ := (449679767039/10000000000000 : ℝ)) half_8_12_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_12_φ1, half_8_12_φ2, half_8_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_12_φ1, half_8_12_φ2, half_8_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_12_φ1, half_8_12_φ2, half_8_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_5 SeedCompletionNinthSecondSeeds.ninth_half_7
    (by simpa only [half_8_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_8_12_hx3)
  exact h.weaken (by norm_num [half_8_12_φ1, half_8_12_φ2, half_8_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_12_hx1 : SourcePowerBound (powerBoxCross 9 7 2 half_8_12_φ1) (85658261945433/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 7) (u := 5) (t := 8)
    (D := 2) (ψ := (707131571969/10000000000000 : ℝ)) half_8_12_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_12_φ1, half_8_12_φ2, half_8_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_12_φ1, half_8_12_φ2, half_8_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_12_φ1, half_8_12_φ2, half_8_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_6 half_8_11
    (by simpa only [half_8_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_8_12_hx2)
  exact h.weaken (by norm_num [half_8_12_φ1, half_8_12_φ2, half_8_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_12 : AdmissibleExponent 9 16 (96039271125897/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 6) (ψ := (49908697983/625000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_7
    (by simpa only [half_8_12_φ1] using half_8_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_8_12_φ1, half_8_12_φ2, half_8_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (168408613947/2000000000000 : ℝ)

private def half_9_12_φ2 : Fin 2 → ℝ := Fin.snoc half_9_12_φ1 (384789138171/5000000000000 : ℝ)

private def half_9_12_φ3 : Fin 3 → ℝ := Fin.snoc half_9_12_φ2 (154756130433/2500000000000 : ℝ)

private theorem half_9_12_hF2 : SourcePowerBound (paddedMoment 9 0 2 8 half_9_12_φ3) (7058062396573/1250000000000 : ℝ) := by
  have h := padded_fourth_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_12_φ3 (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_12_hx3 : SourcePowerBound (powerBoxCross 9 6 8 half_9_12_φ3) (70078357891241/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 6) (r := 2) (v := 8) (w := 8) (D := 8)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_9_12_φ3 (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_12_hF2 half_8_12 half_8_12
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_12_hx2 : SourcePowerBound (powerBoxCross 9 7 4 half_9_12_φ2) (82278017023379/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (154756130433/2500000000000 : ℝ)) half_9_12_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_6 half_8_12
    (by simpa only [half_9_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_12_hx3)
  exact h.weaken (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_12_hx1 : SourcePowerBound (powerBoxCross 9 8 2 half_9_12_φ1) (49397196964121/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (384789138171/5000000000000 : ℝ)) half_9_12_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_7 half_9_11
    (by simpa only [half_9_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_12_hx2)
  exact h.weaken (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_12 : AdmissibleExponent 9 18 (111425039974267/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 7) (ψ := (168408613947/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_8_12
    (by simpa only [half_9_12_φ1] using half_9_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_8_13_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (199634757757/2500000000000 : ℝ)

private def half_8_13_φ2 : Fin 2 → ℝ := Fin.snoc half_8_13_φ1 (353565781353/5000000000000 : ℝ)

private def half_8_13_φ3 : Fin 3 → ℝ := Fin.snoc half_8_13_φ2 (878280719/19531250000 : ℝ)

private theorem half_8_13_hF2 : SourcePowerBound (paddedMoment 9 0 2 8 half_8_13_φ3) (3941974517207/625000000000 : ℝ) := by
  have h := padded_fourth_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_13_φ3 (by norm_num [half_8_13_φ1, half_8_13_φ2, half_8_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_13_φ1, half_8_13_φ2, half_8_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_13_φ1, half_8_13_φ2, half_8_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_13_φ1, half_8_13_φ2, half_8_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_13_hF1 : SourcePowerBound (paddedMoment 9 0 1 8 half_8_13_φ3) (1522324839069/625000000000 : ℝ) := by
  have h := padded_second_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_13_φ3 (by norm_num [half_8_13_φ1, half_8_13_φ2, half_8_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_13_φ1, half_8_13_φ2, half_8_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_13_φ1, half_8_13_φ2, half_8_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_13_φ1, half_8_13_φ2, half_8_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_13_hx3 : SourcePowerBound (powerBoxCross 9 5 8 half_8_13_φ3) (31001974069391/5000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 9) (s := 5) (r := 1) (v := 2) (t := 7) (D := 8)
    (a := (1/14 : ℝ)) (b := (3/14 : ℝ)) (c := (5/7 : ℝ))
    (by norm_num) half_8_13_φ3 (by norm_num [half_8_13_φ1, half_8_13_φ2, half_8_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_13_φ1, half_8_13_φ2, half_8_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_8_13_hF1 half_8_13_hF2 SeedCompletionNinthSecondSeeds.ninth_half_7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_8_13_φ1, half_8_13_φ2, half_8_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_13_hx2 : SourcePowerBound (powerBoxCross 9 6 4 half_8_13_φ2) (3577811521243/500000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 6) (u := 4) (t := 7)
    (D := 4) (ψ := (878280719/19531250000 : ℝ)) half_8_13_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_13_φ1, half_8_13_φ2, half_8_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_13_φ1, half_8_13_φ2, half_8_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_13_φ1, half_8_13_φ2, half_8_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_5 SeedCompletionNinthSecondSeeds.ninth_half_7
    (by simpa only [half_8_13_φ3, show (2:ℝ)*4=8 by norm_num] using half_8_13_hx3)
  exact h.weaken (by norm_num [half_8_13_φ1, half_8_13_φ2, half_8_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_13_hx1 : SourcePowerBound (powerBoxCross 9 7 2 half_8_13_φ1) (685266103367/80000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 7) (u := 5) (t := 8)
    (D := 2) (ψ := (353565781353/5000000000000 : ℝ)) half_8_13_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_13_φ1, half_8_13_φ2, half_8_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_13_φ1, half_8_13_φ2, half_8_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_13_φ1, half_8_13_φ2, half_8_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_6 half_8_12
    (by simpa only [half_8_13_φ2, show (2:ℝ)*2=4 by norm_num] using half_8_13_hx2)
  exact h.weaken (by norm_num [half_8_13_φ1, half_8_13_φ2, half_8_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_13 : AdmissibleExponent 9 16 (96039270324239/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 6) (ψ := (199634757757/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_7
    (by simpa only [half_8_13_φ1] using half_8_13_hx1)
  exact admissibleExponent_mono h (by norm_num [half_8_13_φ1, half_8_13_φ2, half_8_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_13_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (842041660559/10000000000000 : ℝ)

private def half_9_13_φ2 : Fin 2 → ℝ := Fin.snoc half_9_13_φ1 (384789066747/5000000000000 : ℝ)

private def half_9_13_φ3 : Fin 3 → ℝ := Fin.snoc half_9_13_φ2 (24760965597/400000000000 : ℝ)

private theorem half_9_13_hF2 : SourcePowerBound (paddedMoment 9 0 2 8 half_9_13_φ3) (3529034099033/625000000000 : ℝ) := by
  have h := padded_fourth_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_13_φ3 (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_13_hx3 : SourcePowerBound (powerBoxCross 9 6 8 half_9_13_φ3) (70078382956379/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 6) (r := 2) (v := 8) (w := 8) (D := 8)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_9_13_φ3 (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_13_hF2 half_8_13 half_8_13
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_13_hx2 : SourcePowerBound (powerBoxCross 9 7 4 half_9_13_φ2) (82278040780637/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (24760965597/400000000000 : ℝ)) half_9_13_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_6 half_8_13
    (by simpa only [half_9_13_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_13_hx3)
  exact h.weaken (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_13_hx1 : SourcePowerBound (powerBoxCross 9 8 2 half_9_13_φ1) (49397202659269/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (384789066747/5000000000000 : ℝ)) half_9_13_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_7 half_9_12
    (by simpa only [half_9_13_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_13_hx2)
  exact h.weaken (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_13 : AdmissibleExponent 9 18 (111425030226923/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 7) (ψ := (842041660559/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_8_13
    (by simpa only [half_9_13_φ1] using half_9_13_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_8_14_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (798538989387/10000000000000 : ℝ)

private def half_8_14_φ2 : Fin 2 → ℝ := Fin.snoc half_8_14_φ1 (141426311977/2000000000000 : ℝ)

private def half_8_14_φ3 : Fin 3 → ℝ := Fin.snoc half_8_14_φ2 (112419929069/2500000000000 : ℝ)

private theorem half_8_14_hF2 : SourcePowerBound (paddedMoment 9 0 2 8 half_8_14_φ3) (1970987300839/312500000000 : ℝ) := by
  have h := padded_fourth_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_14_φ3 (by norm_num [half_8_14_φ1, half_8_14_φ2, half_8_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_14_φ1, half_8_14_φ2, half_8_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_14_φ1, half_8_14_φ2, half_8_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_14_φ1, half_8_14_φ2, half_8_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_14_hF1 : SourcePowerBound (paddedMoment 9 0 1 8 half_8_14_φ3) (761162433613/312500000000 : ℝ) := by
  have h := padded_second_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_14_φ3 (by norm_num [half_8_14_φ1, half_8_14_φ2, half_8_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_14_φ1, half_8_14_φ2, half_8_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_14_φ1, half_8_14_φ2, half_8_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_14_φ1, half_8_14_φ2, half_8_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_14_hx3 : SourcePowerBound (powerBoxCross 9 5 8 half_8_14_φ3) (31001974393913/5000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 9) (s := 5) (r := 1) (v := 2) (t := 7) (D := 8)
    (a := (1/14 : ℝ)) (b := (3/14 : ℝ)) (c := (5/7 : ℝ))
    (by norm_num) half_8_14_φ3 (by norm_num [half_8_14_φ1, half_8_14_φ2, half_8_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_14_φ1, half_8_14_φ2, half_8_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_8_14_hF1 half_8_14_hF2 SeedCompletionNinthSecondSeeds.ninth_half_7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_8_14_φ1, half_8_14_φ2, half_8_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_14_hx2 : SourcePowerBound (powerBoxCross 9 6 4 half_8_14_φ2) (1788905776369/250000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 6) (u := 4) (t := 7)
    (D := 4) (ψ := (112419929069/2500000000000 : ℝ)) half_8_14_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_14_φ1, half_8_14_φ2, half_8_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_14_φ1, half_8_14_φ2, half_8_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_14_φ1, half_8_14_φ2, half_8_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_5 SeedCompletionNinthSecondSeeds.ninth_half_7
    (by simpa only [half_8_14_φ3, show (2:ℝ)*4=8 by norm_num] using half_8_14_hx3)
  exact h.weaken (by norm_num [half_8_14_φ1, half_8_14_φ2, half_8_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_14_hx1 : SourcePowerBound (powerBoxCross 9 7 2 half_8_14_φ1) (8565826321801/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 7) (u := 5) (t := 8)
    (D := 2) (ψ := (141426311977/2000000000000 : ℝ)) half_8_14_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_14_φ1, half_8_14_φ2, half_8_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_14_φ1, half_8_14_φ2, half_8_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_14_φ1, half_8_14_φ2, half_8_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_6 half_8_13
    (by simpa only [half_8_14_φ2, show (2:ℝ)*2=4 by norm_num] using half_8_14_hx2)
  exact h.weaken (by norm_num [half_8_14_φ1, half_8_14_φ2, half_8_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_14 : AdmissibleExponent 9 16 (96039270080041/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 6) (ψ := (798538989387/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_7
    (by simpa only [half_8_14_φ1] using half_8_14_hx1)
  exact admissibleExponent_mono h (by norm_num [half_8_14_φ1, half_8_14_φ2, half_8_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_14_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (210510294033/2500000000000 : ℝ)

private def half_9_14_φ2 : Fin 2 → ℝ := Fin.snoc half_9_14_φ1 (96197260837/1250000000000 : ℝ)

private def half_9_14_φ3 : Fin 3 → ℝ := Fin.snoc half_9_14_φ2 (309512005799/5000000000000 : ℝ)

private theorem half_9_14_hF2 : SourcePowerBound (paddedMoment 9 0 2 8 half_9_14_φ3) (3529035088361/625000000000 : ℝ) := by
  have h := padded_fourth_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_14_φ3 (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_14_hx3 : SourcePowerBound (powerBoxCross 9 6 8 half_9_14_φ3) (70078391522113/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 6) (r := 2) (v := 8) (w := 8) (D := 8)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_9_14_φ3 (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_14_hF2 half_8_14 half_8_14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_14_hx2 : SourcePowerBound (powerBoxCross 9 7 4 half_9_14_φ2) (20569512232777/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (309512005799/5000000000000 : ℝ)) half_9_14_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_6 half_8_14
    (by simpa only [half_9_14_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_14_hx3)
  exact h.weaken (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_14_hx1 : SourcePowerBound (powerBoxCross 9 8 2 half_9_14_φ1) (98794409262871/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (96197260837/1250000000000 : ℝ)) half_9_14_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_7 half_9_13
    (by simpa only [half_9_14_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_14_hx2)
  exact h.weaken (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_14 : AdmissibleExponent 9 18 (111425026904851/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 7) (ψ := (210510294033/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_8_14
    (by simpa only [half_9_14_φ1] using half_9_14_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_8_15_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (798538976703/10000000000000 : ℝ)

private def half_8_15_φ2 : Fin 2 → ℝ := Fin.snoc half_8_15_φ1 (28285262361/400000000000 : ℝ)

private def half_8_15_φ3 : Fin 3 → ℝ := Fin.snoc half_8_15_φ2 (89935942533/2000000000000 : ℝ)

private theorem half_8_15_hF2 : SourcePowerBound (paddedMoment 9 0 2 8 half_8_15_φ3) (7883949254821/1250000000000 : ℝ) := by
  have h := padded_fourth_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_15_φ3 (by norm_num [half_8_15_φ1, half_8_15_φ2, half_8_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_15_φ1, half_8_15_φ2, half_8_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_15_φ1, half_8_15_φ2, half_8_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_15_φ1, half_8_15_φ2, half_8_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_15_hF1 : SourcePowerBound (paddedMoment 9 0 1 8 half_8_15_φ3) (3044649751607/1250000000000 : ℝ) := by
  have h := padded_second_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_15_φ3 (by norm_num [half_8_15_φ1, half_8_15_φ2, half_8_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_15_φ1, half_8_15_φ2, half_8_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_15_φ1, half_8_15_φ2, half_8_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_15_φ1, half_8_15_φ2, half_8_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_15_hx3 : SourcePowerBound (powerBoxCross 9 5 8 half_8_15_φ3) (12400789797109/2000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 9) (s := 5) (r := 1) (v := 2) (t := 7) (D := 8)
    (a := (1/14 : ℝ)) (b := (3/14 : ℝ)) (c := (5/7 : ℝ))
    (by norm_num) half_8_15_φ3 (by norm_num [half_8_15_φ1, half_8_15_φ2, half_8_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_15_φ1, half_8_15_φ2, half_8_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_8_15_hF1 half_8_15_hF2 SeedCompletionNinthSecondSeeds.ninth_half_7
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_8_15_φ1, half_8_15_φ2, half_8_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_15_hx2 : SourcePowerBound (powerBoxCross 9 6 4 half_8_15_φ2) (894452890583/125000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 6) (u := 4) (t := 7)
    (D := 4) (ψ := (89935942533/2000000000000 : ℝ)) half_8_15_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_15_φ1, half_8_15_φ2, half_8_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_15_φ1, half_8_15_φ2, half_8_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_15_φ1, half_8_15_φ2, half_8_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_5 SeedCompletionNinthSecondSeeds.ninth_half_7
    (by simpa only [half_8_15_φ3, show (2:ℝ)*4=8 by norm_num] using half_8_15_hx3)
  exact h.weaken (by norm_num [half_8_15_φ1, half_8_15_φ2, half_8_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_15_hx1 : SourcePowerBound (powerBoxCross 9 7 2 half_8_15_φ1) (21414565827129/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 7) (u := 5) (t := 8)
    (D := 2) (ψ := (28285262361/400000000000 : ℝ)) half_8_15_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_15_φ1, half_8_15_φ2, half_8_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_15_φ1, half_8_15_φ2, half_8_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_15_φ1, half_8_15_φ2, half_8_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_6 half_8_14
    (by simpa only [half_8_15_φ2, show (2:ℝ)*2=4 by norm_num] using half_8_15_hx2)
  exact h.weaken (by norm_num [half_8_15_φ1, half_8_15_φ2, half_8_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_15 : AdmissibleExponent 9 16 (19207854001131/2000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 6) (ψ := (798538976703/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_7
    (by simpa only [half_8_15_φ1] using half_8_15_hx1)
  exact admissibleExponent_mono h (by norm_num [half_8_15_φ1, half_8_15_φ2, half_8_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_15_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (842041010331/10000000000000 : ℝ)

private def half_9_15_φ2 : Fin 2 → ℝ := Fin.snoc half_9_15_φ1 (153915614271/2000000000000 : ℝ)

private def half_9_15_φ3 : Fin 3 → ℝ := Fin.snoc half_9_15_φ2 (619023968533/10000000000000 : ℝ)

private theorem half_9_15_hF2 : SourcePowerBound (paddedMoment 9 0 2 8 half_9_15_φ3) (7058070849343/1250000000000 : ℝ) := by
  have h := padded_fourth_power (k := 9) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_15_φ3 (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_15_hx3 : SourcePowerBound (powerBoxCross 9 6 8 half_9_15_φ3) (70078394438961/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 9) (s := 6) (r := 2) (v := 8) (w := 8) (D := 8)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_9_15_φ3 (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_15_hF2 half_8_15 half_8_15
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_15_hx2 : SourcePowerBound (powerBoxCross 9 7 4 half_9_15_φ2) (82278051715881/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (619023968533/10000000000000 : ℝ)) half_9_15_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_6 half_8_15
    (by simpa only [half_9_15_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_15_hx3)
  exact h.weaken (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_15_hx1 : SourcePowerBound (powerBoxCross 9 8 2 half_9_15_φ1) (49397205310647/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 9) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (153915614271/2000000000000 : ℝ)) half_9_15_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionNinthSecondSeeds.ninth_half_7 half_9_14
    (by simpa only [half_9_15_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_15_hx2)
  exact h.weaken (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_15 : AdmissibleExponent 9 18 (111425025776259/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 9) (s := 7) (ψ := (842041010331/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_8_15
    (by simpa only [half_9_15_φ1] using half_9_15_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem degree9_half_8 : AdmissibleExponent 9 16 (19207854001131/2000000000000 : ℝ) := half_8_15

theorem source9_entry_8 : AdmissibleExponent 9 16 (Certificate.source9[8]! : ℝ) := by
  apply admissibleExponent_mono degree9_half_8
  norm_num [Certificate.source9,Certificate.Q]

#print axioms source9_entry_8

theorem degree9_half_9 : AdmissibleExponent 9 18 (111425025776259/10000000000000 : ℝ) := half_9_15

theorem source9_entry_9 : AdmissibleExponent 9 18 (Certificate.source9[9]! : ℝ) := by
  apply admissibleExponent_mono degree9_half_9
  norm_num [Certificate.source9,Certificate.Q]

#print axioms source9_entry_9

end Waring.SeedCompletionHigher9SimpleSeeds
