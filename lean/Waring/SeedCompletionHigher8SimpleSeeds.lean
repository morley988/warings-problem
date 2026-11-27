import Waring.SeedCompletionEven8SecondSeeds
import Waring.SeedCompletionGeneralTerminal
import Waring.SeedCompletionNaturalChronological

/-! # Actual degree-8 higher seeds from condition(i)

Every finite stage uses the proved padded second/fourth moments,
literal full-box Holder and the actual all-depth recurrence.
LP calculations select rational witnesses only; all inequalities,
rounding and admissibility are checked by Lean. -/
noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionHigher8SimpleSeeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges

private theorem half_7_00 : AdmissibleExponent 8 14 (42497871252989/5000000000000 : ℝ) := by
  have h := endpoint_admissible (s := 5) (by norm_num : 0 < (8 : ℕ))
    SeedCompletionEven8SecondSeeds.degree8_half_6 (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_8_00 : AdmissibleExponent 8 16 (101871274692731/10000000000000 : ℝ) := by
  have h := endpoint_admissible (s := 6) (by norm_num : 0 < (8 : ℕ))
    half_7_00 (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private theorem half_9_00 : AdmissibleExponent 8 18 (5956868267807/500000000000 : ℝ) := by
  have h := endpoint_admissible (s := 7) (by norm_num : 0 < (8 : ℕ))
    half_8_00 (by norm_num)
  exact admissibleExponent_mono h (by norm_num)

private def half_7_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1003093605909/10000000000000 : ℝ)

private def half_7_01_φ2 : Fin 2 → ℝ := Fin.snoc half_7_01_φ1 (787383796151/10000000000000 : ℝ)

private def half_7_01_φ3 : Fin 3 → ℝ := Fin.snoc half_7_01_φ2 (491410188303/10000000000000 : ℝ)

private theorem half_7_01_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_7_01_φ3) (62080360602377/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_01_φ3 (by norm_num [half_7_01_φ1, half_7_01_φ2, half_7_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_01_φ1, half_7_01_φ2, half_7_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_01_φ1, half_7_01_φ2, half_7_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_7_01_φ1, half_7_01_φ2, half_7_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_7_01_hF1 : SourcePowerBound (paddedMoment 8 0 1 8 half_7_01_φ3) (24026786867459/10000000000000 : ℝ) := by
  have h := padded_second_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_01_φ3 (by norm_num [half_7_01_φ1, half_7_01_φ2, half_7_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_01_φ1, half_7_01_φ2, half_7_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_01_φ1, half_7_01_φ2, half_7_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_7_01_φ1, half_7_01_φ2, half_7_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_7_01_hx3 : SourcePowerBound (powerBoxCross 8 4 8 half_7_01_φ3) (25250701819323/5000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 8) (s := 4) (r := 1) (v := 2) (t := 7) (D := 8)
    (a := (5/14 : ℝ)) (b := (1/14 : ℝ)) (c := (4/7 : ℝ))
    (by norm_num) half_7_01_φ3 (by norm_num [half_7_01_φ1, half_7_01_φ2, half_7_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_01_φ1, half_7_01_φ2, half_7_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_7_01_hF1 half_7_01_hF2 half_7_00
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_7_01_φ1, half_7_01_φ2, half_7_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_01_hx2 : SourcePowerBound (powerBoxCross 8 5 4 half_7_01_φ2) (58848903935917/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 5) (u := 3) (t := 6)
    (D := 4) (ψ := (491410188303/10000000000000 : ℝ)) half_7_01_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_7_01_φ1, half_7_01_φ2, half_7_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_01_φ1, half_7_01_φ2, half_7_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_7_01_φ1, half_7_01_φ2, half_7_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_4 SeedCompletionEven8SecondSeeds.degree8_half_6
    (by simpa only [half_7_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_7_01_hx3)
  exact h.weaken (by norm_num [half_7_01_φ1, half_7_01_φ2, half_7_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_01_hx1 : SourcePowerBound (powerBoxCross 8 6 2 half_7_01_φ1) (18172947097771/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 6) (u := 4) (t := 7)
    (D := 2) (ψ := (787383796151/10000000000000 : ℝ)) half_7_01_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_7_01_φ1, half_7_01_φ2, half_7_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_01_φ1, half_7_01_φ2, half_7_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_7_01_φ1, half_7_01_φ2, half_7_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_5 half_7_00
    (by simpa only [half_7_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_7_01_hx2)
  exact h.weaken (by norm_num [half_7_01_φ1, half_7_01_φ2, half_7_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_01 : AdmissibleExponent 8 14 (83725818056083/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 5) (ψ := (1003093605909/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6
    (by simpa only [half_7_01_φ1] using half_7_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_7_01_φ1, half_7_01_φ2, half_7_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_8_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (53706563571/500000000000 : ℝ)

private def half_8_01_φ2 : Fin 2 → ℝ := Fin.snoc half_8_01_φ1 (175786662737/2000000000000 : ℝ)

private def half_8_01_φ3 : Fin 3 → ℝ := Fin.snoc half_8_01_φ2 (631956756483/10000000000000 : ℝ)

private theorem half_8_01_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_8_01_φ3) (13928637956663/2500000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_01_φ3 (by norm_num [half_8_01_φ1, half_8_01_φ2, half_8_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_01_φ1, half_8_01_φ2, half_8_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_01_φ1, half_8_01_φ2, half_8_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_01_φ1, half_8_01_φ2, half_8_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_01_hx3 : SourcePowerBound (powerBoxCross 8 5 8 half_8_01_φ3) (28840192833393/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 5) (r := 2) (v := 6) (w := 7) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_8_01_φ3 (by norm_num [half_8_01_φ1, half_8_01_φ2, half_8_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_01_φ1, half_8_01_φ2, half_8_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_8_01_hF2 SeedCompletionEven8SecondSeeds.degree8_half_6 half_7_01
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_8_01_φ1, half_8_01_φ2, half_8_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_01_hx2 : SourcePowerBound (powerBoxCross 8 6 4 half_8_01_φ2) (68535084712527/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 6) (u := 4) (t := 7)
    (D := 4) (ψ := (631956756483/10000000000000 : ℝ)) half_8_01_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_01_φ1, half_8_01_φ2, half_8_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_01_φ1, half_8_01_φ2, half_8_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_01_φ1, half_8_01_φ2, half_8_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_5 half_7_01
    (by simpa only [half_8_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_8_01_hx3)
  exact h.weaken (by norm_num [half_8_01_φ1, half_8_01_φ2, half_8_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_01_hx1 : SourcePowerBound (powerBoxCross 8 7 2 half_8_01_φ1) (85806697387583/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 7) (u := 5) (t := 8)
    (D := 2) (ψ := (175786662737/2000000000000 : ℝ)) half_8_01_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_01_φ1, half_8_01_φ2, half_8_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_01_φ1, half_8_01_φ2, half_8_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_01_φ1, half_8_01_φ2, half_8_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6 half_8_00
    (by simpa only [half_8_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_8_01_hx2)
  exact h.weaken (by norm_num [half_8_01_φ1, half_8_01_φ2, half_8_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_01 : AdmissibleExponent 8 16 (99770403916043/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 6) (ψ := (53706563571/500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_7_01
    (by simpa only [half_8_01_φ1] using half_8_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_8_01_φ1, half_8_01_φ2, half_8_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_01_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (57235941137/500000000000 : ℝ)

private def half_9_01_φ2 : Fin 2 → ℝ := Fin.snoc half_9_01_φ1 (59679279027/625000000000 : ℝ)

private def half_9_01_φ3 : Fin 3 → ℝ := Fin.snoc half_9_01_φ2 (890169492751/10000000000000 : ℝ)

private theorem half_9_01_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_9_01_φ3) (47215107621617/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_01_φ3 (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_01_hx3 : SourcePowerBound (powerBoxCross 8 6 8 half_9_01_φ3) (8032485840833/1250000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 6) (r := 2) (v := 8) (w := 8) (D := 8)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_9_01_φ3 (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_01_hF2 half_8_01 half_8_01
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_01_hx2 : SourcePowerBound (powerBoxCross 8 7 4 half_9_01_φ2) (19772172110369/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (890169492751/10000000000000 : ℝ)) half_9_01_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6 half_8_01
    (by simpa only [half_9_01_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_01_hx3)
  exact h.weaken (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_01_hx1 : SourcePowerBound (powerBoxCross 8 8 2 half_9_01_φ1) (19898843361457/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (59679279027/625000000000 : ℝ)) half_9_01_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_7_01 half_9_00
    (by simpa only [half_9_01_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_01_hx2)
  exact h.weaken (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_01 : AdmissibleExponent 8 18 (23332999829677/2000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 7) (ψ := (57235941137/500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_8_01
    (by simpa only [half_9_01_φ1] using half_9_01_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_01_φ1, half_9_01_φ2, half_9_01_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_7_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (92255974119/1000000000000 : ℝ)

private def half_7_02_φ2 : Fin 2 → ℝ := Fin.snoc half_7_02_φ1 (23509530083/312500000000 : ℝ)

private def half_7_02_φ3 : Fin 3 → ℝ := Fin.snoc half_7_02_φ2 (340315912541/10000000000000 : ℝ)

private theorem half_7_02_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_7_02_φ3) (67681207055873/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_02_φ3 (by norm_num [half_7_02_φ1, half_7_02_φ2, half_7_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_02_φ1, half_7_02_φ2, half_7_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_02_φ1, half_7_02_φ2, half_7_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_7_02_φ1, half_7_02_φ2, half_7_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_7_02_hF1 : SourcePowerBound (paddedMoment 8 0 1 8 half_7_02_φ3) (25893735685291/10000000000000 : ℝ) := by
  have h := padded_second_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_02_φ3 (by norm_num [half_7_02_φ1, half_7_02_φ2, half_7_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_02_φ1, half_7_02_φ2, half_7_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_02_φ1, half_7_02_φ2, half_7_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_7_02_φ1, half_7_02_φ2, half_7_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_7_02_hx3 : SourcePowerBound (powerBoxCross 8 4 8 half_7_02_φ3) (26142082622171/5000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 8) (s := 4) (r := 1) (v := 2) (t := 7) (D := 8)
    (a := (5/14 : ℝ)) (b := (1/14 : ℝ)) (c := (4/7 : ℝ))
    (by norm_num) half_7_02_φ3 (by norm_num [half_7_02_φ1, half_7_02_φ2, half_7_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_02_φ1, half_7_02_φ2, half_7_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_7_02_hF1 half_7_02_hF2 half_7_01
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_7_02_φ1, half_7_02_φ2, half_7_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_02_hx2 : SourcePowerBound (powerBoxCross 8 5 4 half_7_02_φ2) (30006228742173/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 5) (u := 3) (t := 6)
    (D := 4) (ψ := (340315912541/10000000000000 : ℝ)) half_7_02_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_7_02_φ1, half_7_02_φ2, half_7_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_02_φ1, half_7_02_φ2, half_7_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_7_02_φ1, half_7_02_φ2, half_7_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_4 SeedCompletionEven8SecondSeeds.degree8_half_6
    (by simpa only [half_7_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_7_02_hx3)
  exact h.weaken (by norm_num [half_7_02_φ1, half_7_02_φ2, half_7_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_02_hx1 : SourcePowerBound (powerBoxCross 8 6 2 half_7_02_φ1) (14632689511233/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 6) (u := 4) (t := 7)
    (D := 2) (ψ := (23509530083/312500000000 : ℝ)) half_7_02_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_7_02_φ1, half_7_02_φ2, half_7_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_02_φ1, half_7_02_φ2, half_7_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_7_02_φ1, half_7_02_φ2, half_7_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_5 half_7_01
    (by simpa only [half_7_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_7_02_hx2)
  exact h.weaken (by norm_num [half_7_02_φ1, half_7_02_φ2, half_7_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_02 : AdmissibleExponent 8 14 (16662320941851/2000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 5) (ψ := (92255974119/1000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6
    (by simpa only [half_7_02_φ1] using half_7_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_7_02_φ1, half_7_02_φ2, half_7_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_8_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (993352119337/10000000000000 : ℝ)

private def half_8_02_φ2 : Fin 2 → ℝ := Fin.snoc half_8_02_φ1 (105721910707/1250000000000 : ℝ)

private def half_8_02_φ3 : Fin 3 → ℝ := Fin.snoc half_8_02_φ2 (585448203783/10000000000000 : ℝ)

private theorem half_8_02_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_8_02_φ3) (7385489026963/1250000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_02_φ3 (by norm_num [half_8_02_φ1, half_8_02_φ2, half_8_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_02_φ1, half_8_02_φ2, half_8_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_02_φ1, half_8_02_φ2, half_8_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_02_φ1, half_8_02_φ2, half_8_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_02_hx3 : SourcePowerBound (powerBoxCross 8 5 8 half_8_02_φ3) (11862507298361/2000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 5) (r := 2) (v := 6) (w := 7) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_8_02_φ3 (by norm_num [half_8_02_φ1, half_8_02_φ2, half_8_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_02_φ1, half_8_02_φ2, half_8_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_8_02_hF2 SeedCompletionEven8SecondSeeds.degree8_half_6 half_7_02
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_8_02_φ1, half_8_02_φ2, half_8_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_02_hx2 : SourcePowerBound (powerBoxCross 8 6 4 half_8_02_φ2) (34924304415671/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 6) (u := 4) (t := 7)
    (D := 4) (ψ := (585448203783/10000000000000 : ℝ)) half_8_02_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_02_φ1, half_8_02_φ2, half_8_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_02_φ1, half_8_02_φ2, half_8_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_02_φ1, half_8_02_φ2, half_8_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_5 half_7_02
    (by simpa only [half_8_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_8_02_hx3)
  exact h.weaken (by norm_num [half_8_02_φ1, half_8_02_φ2, half_8_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_02_hx1 : SourcePowerBound (powerBoxCross 8 7 2 half_8_02_φ1) (43014590459133/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 7) (u := 5) (t := 8)
    (D := 2) (ψ := (105721910707/1250000000000 : ℝ)) half_8_02_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_02_φ1, half_8_02_φ2, half_8_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_02_φ1, half_8_02_φ2, half_8_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_02_φ1, half_8_02_φ2, half_8_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6 half_8_01
    (by simpa only [half_8_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_8_02_hx2)
  exact h.weaken (by norm_num [half_8_02_φ1, half_8_02_φ2, half_8_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_02 : AdmissibleExponent 8 16 (98942758469647/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 6) (ψ := (993352119337/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_7_02
    (by simpa only [half_8_02_φ1] using half_8_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_8_02_φ1, half_8_02_φ2, half_8_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_02_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1070976250053/10000000000000 : ℝ)

private def half_9_02_φ2 : Fin 2 → ℝ := Fin.snoc half_9_02_φ1 (929376020987/10000000000000 : ℝ)

private def half_9_02_φ3 : Fin 3 → ℝ := Fin.snoc half_9_02_φ2 (809037515393/10000000000000 : ℝ)

private theorem half_9_02_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_9_02_φ3) (51002814484907/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_02_φ3 (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_02_hx3 : SourcePowerBound (powerBoxCross 8 6 8 half_9_02_φ3) (33055057171001/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 6) (r := 2) (v := 8) (w := 8) (D := 8)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_9_02_φ3 (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_02_hF2 half_8_02 half_8_02
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_02_hx2 : SourcePowerBound (powerBoxCross 8 7 4 half_9_02_φ2) (4003944560573/500000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (809037515393/10000000000000 : ℝ)) half_9_02_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6 half_8_02
    (by simpa only [half_9_02_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_02_hx3)
  exact h.weaken (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_02_hx1 : SourcePowerBound (powerBoxCross 8 8 2 half_9_02_φ1) (49708600138067/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (929376020987/10000000000000 : ℝ)) half_9_02_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_7_02 half_9_01
    (by simpa only [half_9_02_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_02_hx2)
  exact h.weaken (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_02 : AdmissibleExponent 8 18 (115481844026929/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 7) (ψ := (1070976250053/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_8_02
    (by simpa only [half_9_02_φ1] using half_9_02_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_02_φ1, half_9_02_φ2, half_9_02_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_7_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (44794704421/500000000000 : ℝ)

private def half_7_03_φ2 : Fin 2 → ℝ := Fin.snoc half_7_03_φ1 (740423112973/10000000000000 : ℝ)

private def half_7_03_φ3 : Fin 3 → ℝ := Fin.snoc half_7_03_φ2 (57830412189/2000000000000 : ℝ)

private theorem half_7_03_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_7_03_φ3) (34782572745451/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_03_φ3 (by norm_num [half_7_03_φ1, half_7_03_φ2, half_7_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_03_φ1, half_7_03_φ2, half_7_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_03_φ1, half_7_03_φ2, half_7_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_7_03_φ1, half_7_03_φ2, half_7_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_7_03_hF1 : SourcePowerBound (paddedMoment 8 0 1 8 half_7_03_φ3) (13260857581817/5000000000000 : ℝ) := by
  have h := padded_second_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_03_φ3 (by norm_num [half_7_03_φ1, half_7_03_φ2, half_7_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_03_φ1, half_7_03_φ2, half_7_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_03_φ1, half_7_03_φ2, half_7_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_7_03_φ1, half_7_03_φ2, half_7_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_7_03_hx3 : SourcePowerBound (powerBoxCross 8 4 8 half_7_03_φ3) (5288110083801/1000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 8) (s := 4) (r := 1) (v := 2) (t := 7) (D := 8)
    (a := (5/14 : ℝ)) (b := (1/14 : ℝ)) (c := (4/7 : ℝ))
    (by norm_num) half_7_03_φ3 (by norm_num [half_7_03_φ1, half_7_03_φ2, half_7_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_03_φ1, half_7_03_φ2, half_7_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_7_03_hF1 half_7_03_hF2 half_7_02
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_7_03_φ1, half_7_03_φ2, half_7_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_03_hx2 : SourcePowerBound (powerBoxCross 8 5 4 half_7_03_φ2) (60398921546689/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 5) (u := 3) (t := 6)
    (D := 4) (ψ := (57830412189/2000000000000 : ℝ)) half_7_03_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_7_03_φ1, half_7_03_φ2, half_7_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_03_φ1, half_7_03_φ2, half_7_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_7_03_φ1, half_7_03_φ2, half_7_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_4 SeedCompletionEven8SecondSeeds.degree8_half_6
    (by simpa only [half_7_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_7_03_hx3)
  exact h.weaken (by norm_num [half_7_03_φ1, half_7_03_φ2, half_7_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_03_hx1 : SourcePowerBound (powerBoxCross 8 6 2 half_7_03_φ1) (73319619119091/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 6) (u := 4) (t := 7)
    (D := 2) (ψ := (740423112973/10000000000000 : ℝ)) half_7_03_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_7_03_φ1, half_7_03_φ2, half_7_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_03_φ1, half_7_03_φ2, half_7_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_7_03_φ1, half_7_03_φ2, half_7_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_5 half_7_02
    (by simpa only [half_7_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_7_03_hx2)
  exact h.weaken (by norm_num [half_7_03_φ1, half_7_03_φ2, half_7_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_03 : AdmissibleExponent 8 14 (83174454091711/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 5) (ψ := (44794704421/500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6
    (by simpa only [half_7_03_φ1] using half_7_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_7_03_φ1, half_7_03_φ2, half_7_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_8_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (479360333199/5000000000000 : ℝ)

private def half_8_03_φ2 : Fin 2 → ℝ := Fin.snoc half_8_03_φ1 (417079720697/5000000000000 : ℝ)

private def half_8_03_φ3 : Fin 3 → ℝ := Fin.snoc half_8_03_φ2 (284034525787/5000000000000 : ℝ)

private theorem half_8_03_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_8_03_φ3) (30210033826657/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_03_φ3 (by norm_num [half_8_03_φ1, half_8_03_φ2, half_8_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_03_φ1, half_8_03_φ2, half_8_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_03_φ1, half_8_03_φ2, half_8_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_03_φ1, half_8_03_φ2, half_8_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_03_hx3 : SourcePowerBound (powerBoxCross 8 5 8 half_8_03_φ3) (59968297577893/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 5) (r := 2) (v := 6) (w := 7) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_8_03_φ3 (by norm_num [half_8_03_φ1, half_8_03_φ2, half_8_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_03_φ1, half_8_03_φ2, half_8_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_8_03_hF2 SeedCompletionEven8SecondSeeds.degree8_half_6 half_7_03
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_8_03_φ1, half_8_03_φ2, half_8_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_03_hx2 : SourcePowerBound (powerBoxCross 8 6 4 half_8_03_φ2) (70396514978739/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 6) (u := 4) (t := 7)
    (D := 4) (ψ := (284034525787/5000000000000 : ℝ)) half_8_03_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_03_φ1, half_8_03_φ2, half_8_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_03_φ1, half_8_03_φ2, half_8_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_03_φ1, half_8_03_φ2, half_8_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_5 half_7_03
    (by simpa only [half_8_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_8_03_hx3)
  exact h.weaken (by norm_num [half_8_03_φ1, half_8_03_φ2, half_8_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_03_hx1 : SourcePowerBound (powerBoxCross 8 7 2 half_8_03_φ1) (1346235436761/156250000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 7) (u := 5) (t := 8)
    (D := 2) (ψ := (417079720697/5000000000000 : ℝ)) half_8_03_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_03_φ1, half_8_03_φ2, half_8_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_03_φ1, half_8_03_φ2, half_8_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_03_φ1, half_8_03_φ2, half_8_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6 half_8_02
    (by simpa only [half_8_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_8_03_hx2)
  exact h.weaken (by norm_num [half_8_03_φ1, half_8_03_φ2, half_8_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_03 : AdmissibleExponent 8 16 (49311218307939/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 6) (ψ := (479360333199/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_7_03
    (by simpa only [half_8_03_φ1] using half_8_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_8_03_φ1, half_8_03_φ2, half_8_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_03_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (41178973857/400000000000 : ℝ)

private def half_9_03_φ2 : Fin 2 → ℝ := Fin.snoc half_9_03_φ1 (916043505437/10000000000000 : ℝ)

private def half_9_03_φ3 : Fin 3 → ℝ := Fin.snoc half_9_03_φ2 (773824631141/10000000000000 : ℝ)

private theorem half_9_03_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_9_03_φ3) (52893807856937/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_03_φ3 (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_03_hx3 : SourcePowerBound (powerBoxCross 8 6 8 half_9_03_φ3) (67076165801131/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 6) (r := 2) (v := 8) (w := 8) (D := 8)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_9_03_φ3 (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_03_hF2 half_8_03 half_8_03
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_03_hx2 : SourcePowerBound (powerBoxCross 8 7 4 half_9_03_φ2) (20175609661687/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (773824631141/10000000000000 : ℝ)) half_9_03_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6 half_8_03
    (by simpa only [half_9_03_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_03_hx3)
  exact h.weaken (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_03_hx1 : SourcePowerBound (powerBoxCross 8 8 2 half_9_03_φ1) (99498984114513/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (916043505437/10000000000000 : ℝ)) half_9_03_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_7_03 half_9_02
    (by simpa only [half_9_03_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_03_hx2)
  exact h.weaken (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_03 : AdmissibleExponent 8 18 (14367637413861/1250000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 7) (ψ := (41178973857/400000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_8_03
    (by simpa only [half_9_03_φ1] using half_9_03_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_03_φ1, half_9_03_φ2, half_9_03_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_7_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (887020750973/10000000000000 : ℝ)

private def half_7_04_φ2 : Fin 2 → ℝ := Fin.snoc half_7_04_φ1 (368219816627/5000000000000 : ℝ)

private def half_7_04_φ3 : Fin 3 → ℝ := Fin.snoc half_7_04_φ2 (272000576311/10000000000000 : ℝ)

private theorem half_7_04_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_7_04_φ3) (35097659914351/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_04_φ3 (by norm_num [half_7_04_φ1, half_7_04_φ2, half_7_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_04_φ1, half_7_04_φ2, half_7_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_04_φ1, half_7_04_φ2, half_7_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_7_04_φ1, half_7_04_φ2, half_7_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_7_04_hF1 : SourcePowerBound (paddedMoment 8 0 1 8 half_7_04_φ3) (13365886638117/5000000000000 : ℝ) := by
  have h := padded_second_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_04_φ3 (by norm_num [half_7_04_φ1, half_7_04_φ2, half_7_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_04_φ1, half_7_04_φ2, half_7_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_04_φ1, half_7_04_φ2, half_7_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_7_04_φ1, half_7_04_φ2, half_7_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_7_04_hx3 : SourcePowerBound (powerBoxCross 8 4 8 half_7_04_φ3) (414691224569/78125000000 : ℝ) := by
  have h := full_B_cross_power (k := 8) (s := 4) (r := 1) (v := 2) (t := 7) (D := 8)
    (a := (5/14 : ℝ)) (b := (1/14 : ℝ)) (c := (4/7 : ℝ))
    (by norm_num) half_7_04_φ3 (by norm_num [half_7_04_φ1, half_7_04_φ2, half_7_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_04_φ1, half_7_04_φ2, half_7_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_7_04_hF1 half_7_04_hF2 half_7_03
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_7_04_φ1, half_7_04_φ2, half_7_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_04_hx2 : SourcePowerBound (powerBoxCross 8 5 4 half_7_04_φ2) (15131913888021/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 5) (u := 3) (t := 6)
    (D := 4) (ψ := (272000576311/10000000000000 : ℝ)) half_7_04_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_7_04_φ1, half_7_04_φ2, half_7_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_04_φ1, half_7_04_φ2, half_7_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_7_04_φ1, half_7_04_φ2, half_7_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_4 SeedCompletionEven8SecondSeeds.degree8_half_6
    (by simpa only [half_7_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_7_04_hx3)
  exact h.weaken (by norm_num [half_7_04_φ1, half_7_04_φ2, half_7_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_04_hx1 : SourcePowerBound (powerBoxCross 8 6 2 half_7_04_φ1) (36685793603313/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 6) (u := 4) (t := 7)
    (D := 2) (ψ := (368219816627/5000000000000 : ℝ)) half_7_04_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_7_04_φ1, half_7_04_φ2, half_7_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_04_φ1, half_7_04_φ2, half_7_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_7_04_φ1, half_7_04_φ2, half_7_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_5 half_7_03
    (by simpa only [half_7_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_7_04_hx2)
  exact h.weaken (by norm_num [half_7_04_φ1, half_7_04_φ2, half_7_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_04 : AdmissibleExponent 8 14 (83128815467329/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 5) (ψ := (887020750973/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6
    (by simpa only [half_7_04_φ1] using half_7_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_7_04_φ1, half_7_04_φ2, half_7_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_8_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (472280966499/5000000000000 : ℝ)

private def half_8_04_φ2 : Fin 2 → ℝ := Fin.snoc half_8_04_φ1 (103765083277/1250000000000 : ℝ)

private def half_8_04_φ3 : Fin 3 → ℝ := Fin.snoc half_8_04_φ2 (17552374061/312500000000 : ℝ)

private theorem half_8_04_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_8_04_φ3) (30468235023757/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_04_φ3 (by norm_num [half_8_04_φ1, half_8_04_φ2, half_8_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_04_φ1, half_8_04_φ2, half_8_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_04_φ1, half_8_04_φ2, half_8_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_04_φ1, half_8_04_φ2, half_8_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_04_hx3 : SourcePowerBound (powerBoxCross 8 5 8 half_8_04_φ3) (30112164012907/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 5) (r := 2) (v := 6) (w := 7) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_8_04_φ3 (by norm_num [half_8_04_φ1, half_8_04_φ2, half_8_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_04_φ1, half_8_04_φ2, half_8_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_8_04_hF2 SeedCompletionEven8SecondSeeds.degree8_half_6 half_7_04
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_8_04_φ1, half_8_04_φ2, half_8_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_04_hx2 : SourcePowerBound (powerBoxCross 8 6 4 half_8_04_φ2) (1412327227979/200000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 6) (u := 4) (t := 7)
    (D := 4) (ψ := (17552374061/312500000000 : ℝ)) half_8_04_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_04_φ1, half_8_04_φ2, half_8_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_04_φ1, half_8_04_φ2, half_8_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_04_φ1, half_8_04_φ2, half_8_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_5 half_7_04
    (by simpa only [half_8_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_8_04_hx3)
  exact h.weaken (by norm_num [half_8_04_φ1, half_8_04_φ2, half_8_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_04_hx1 : SourcePowerBound (powerBoxCross 8 7 2 half_8_04_φ1) (43110672968883/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 7) (u := 5) (t := 8)
    (D := 2) (ψ := (103765083277/1250000000000 : ℝ)) half_8_04_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_04_φ1, half_8_04_φ2, half_8_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_04_φ1, half_8_04_φ2, half_8_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_04_φ1, half_8_04_φ2, half_8_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6 half_8_03
    (by simpa only [half_8_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_8_04_hx2)
  exact h.weaken (by norm_num [half_8_04_φ1, half_8_04_φ2, half_8_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_04 : AdmissibleExponent 8 16 (4925032553337/500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 6) (ψ := (472280966499/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_7_04
    (by simpa only [half_8_04_φ1] using half_8_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_8_04_φ1, half_8_04_φ2, half_8_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_04_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1008481177411/10000000000000 : ℝ)

private def half_9_04_φ2 : Fin 2 → ℝ := Fin.snoc half_9_04_φ1 (454962720593/5000000000000 : ℝ)

private def half_9_04_φ3 : Fin 3 → ℝ := Fin.snoc half_9_04_φ2 (94892914467/1250000000000 : ℝ)

private theorem half_9_04_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_9_04_φ3) (53771451379007/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_04_φ3 (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_04_hx3 : SourcePowerBound (powerBoxCross 8 6 8 half_9_04_φ3) (4221113766259/625000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 6) (r := 2) (v := 8) (w := 8) (D := 8)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_9_04_φ3 (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_04_hF2 half_8_04 half_8_04
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_04_hx2 : SourcePowerBound (powerBoxCross 8 7 4 half_9_04_φ2) (40515942843887/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (94892914467/1250000000000 : ℝ)) half_9_04_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6 half_8_04
    (by simpa only [half_9_04_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_04_hx3)
  exact h.weaken (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_04_hx1 : SourcePowerBound (powerBoxCross 8 8 2 half_9_04_φ1) (24893881746951/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (454962720593/5000000000000 : ℝ)) half_9_04_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_7_04 half_9_03
    (by simpa only [half_9_04_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_04_hx2)
  exact h.weaken (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_04 : AdmissibleExponent 8 18 (114702744648969/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 7) (ψ := (1008481177411/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_8_04
    (by simpa only [half_9_04_φ1] using half_9_04_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_04_φ1, half_9_04_φ2, half_9_04_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_7_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (221015785257/2500000000000 : ℝ)

private def half_7_05_φ2 : Fin 2 → ℝ := Fin.snoc half_7_05_φ1 (367554293063/5000000000000 : ℝ)

private def half_7_05_φ3 : Fin 3 → ℝ := Fin.snoc half_7_05_φ2 (5325394457/200000000000 : ℝ)

private theorem half_7_05_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_7_05_φ3) (17601432387479/2500000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_05_φ3 (by norm_num [half_7_05_φ1, half_7_05_φ2, half_7_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_05_φ1, half_7_05_φ2, half_7_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_05_φ1, half_7_05_φ2, half_7_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_7_05_φ1, half_7_05_φ2, half_7_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_7_05_hF1 : SourcePowerBound (paddedMoment 8 0 1 8 half_7_05_φ3) (6700477462493/2500000000000 : ℝ) := by
  have h := padded_second_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_05_φ3 (by norm_num [half_7_05_φ1, half_7_05_φ2, half_7_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_05_φ1, half_7_05_φ2, half_7_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_05_φ1, half_7_05_φ2, half_7_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_7_05_φ1, half_7_05_φ2, half_7_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_7_05_hx3 : SourcePowerBound (powerBoxCross 8 4 8 half_7_05_φ3) (26573506822891/5000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 8) (s := 4) (r := 1) (v := 2) (t := 7) (D := 8)
    (a := (5/14 : ℝ)) (b := (1/14 : ℝ)) (c := (4/7 : ℝ))
    (by norm_num) half_7_05_φ3 (by norm_num [half_7_05_φ1, half_7_05_φ2, half_7_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_05_φ1, half_7_05_φ2, half_7_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_7_05_hF1 half_7_05_hF2 half_7_04
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_7_05_φ1, half_7_05_φ2, half_7_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_05_hx2 : SourcePowerBound (powerBoxCross 8 5 4 half_7_05_φ2) (60570579238941/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 5) (u := 3) (t := 6)
    (D := 4) (ψ := (5325394457/200000000000 : ℝ)) half_7_05_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_7_05_φ1, half_7_05_φ2, half_7_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_05_φ1, half_7_05_φ2, half_7_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_7_05_φ1, half_7_05_φ2, half_7_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_4 SeedCompletionEven8SecondSeeds.degree8_half_6
    (by simpa only [half_7_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_7_05_hx3)
  exact h.weaken (by norm_num [half_7_05_φ1, half_7_05_φ2, half_7_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_05_hx1 : SourcePowerBound (powerBoxCross 8 6 2 half_7_05_φ1) (14677781782301/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 6) (u := 4) (t := 7)
    (D := 2) (ψ := (367554293063/5000000000000 : ℝ)) half_7_05_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_7_05_φ1, half_7_05_φ2, half_7_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_05_φ1, half_7_05_φ2, half_7_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_7_05_φ1, half_7_05_φ2, half_7_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_5 half_7_04
    (by simpa only [half_7_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_7_05_hx2)
  exact h.weaken (by norm_num [half_7_05_φ1, half_7_05_φ2, half_7_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_05 : AdmissibleExponent 8 14 (83113603462813/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 5) (ψ := (221015785257/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6
    (by simpa only [half_7_05_φ1] using half_7_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_7_05_φ1, half_7_05_φ2, half_7_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_8_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (469485533991/5000000000000 : ℝ)

private def half_8_05_φ2 : Fin 2 → ℝ := Fin.snoc half_8_05_φ1 (414361215917/5000000000000 : ℝ)

private def half_8_05_φ3 : Fin 3 → ℝ := Fin.snoc half_8_05_φ2 (559350160421/10000000000000 : ℝ)

private theorem half_8_05_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_8_05_φ3) (61132083135023/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_05_φ3 (by norm_num [half_8_05_φ1, half_8_05_φ2, half_8_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_05_φ1, half_8_05_φ2, half_8_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_05_φ1, half_8_05_φ2, half_8_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_05_φ1, half_8_05_φ2, half_8_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_05_hx3 : SourcePowerBound (powerBoxCross 8 5 8 half_8_05_φ3) (12064415878971/2000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 5) (r := 2) (v := 6) (w := 7) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_8_05_φ3 (by norm_num [half_8_05_φ1, half_8_05_φ2, half_8_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_05_φ1, half_8_05_φ2, half_8_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_8_05_hF2 SeedCompletionEven8SecondSeeds.degree8_half_6 half_7_05
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_8_05_φ1, half_8_05_φ2, half_8_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_05_hx2 : SourcePowerBound (powerBoxCross 8 6 4 half_8_05_φ2) (35351010535999/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 6) (u := 4) (t := 7)
    (D := 4) (ψ := (559350160421/10000000000000 : ℝ)) half_8_05_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_05_φ1, half_8_05_φ2, half_8_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_05_φ1, half_8_05_φ2, half_8_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_05_φ1, half_8_05_φ2, half_8_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_5 half_7_05
    (by simpa only [half_8_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_8_05_hx3)
  exact h.weaken (by norm_num [half_8_05_φ1, half_8_05_φ2, half_8_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_05_hx1 : SourcePowerBound (powerBoxCross 8 7 2 half_8_05_φ1) (86248447630067/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 7) (u := 5) (t := 8)
    (D := 2) (ψ := (414361215917/5000000000000 : ℝ)) half_8_05_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_05_φ1, half_8_05_φ2, half_8_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_05_φ1, half_8_05_φ2, half_8_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_05_φ1, half_8_05_φ2, half_8_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6 half_8_04
    (by simpa only [half_8_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_8_05_hx2)
  exact h.weaken (by norm_num [half_8_05_φ1, half_8_05_φ2, half_8_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_05 : AdmissibleExponent 8 16 (98455071513833/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 6) (ψ := (469485533991/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_7_05
    (by simpa only [half_8_05_φ1] using half_8_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_8_05_φ1, half_8_05_φ2, half_8_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_05_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (998566506411/10000000000000 : ℝ)

private def half_9_05_φ2 : Fin 2 → ℝ := Fin.snoc half_9_05_φ1 (453654119187/5000000000000 : ℝ)

private def half_9_05_φ3 : Fin 3 → ℝ := Fin.snoc half_9_05_φ2 (376594730907/5000000000000 : ℝ)

private theorem half_9_05_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_9_05_φ3) (54159651661421/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_05_φ3 (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_05_hx3 : SourcePowerBound (powerBoxCross 8 6 8 half_9_05_φ3) (67746339804187/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 6) (r := 2) (v := 8) (w := 8) (D := 8)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_9_05_φ3 (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_05_hF2 half_8_05 half_8_05
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_05_hx2 : SourcePowerBound (powerBoxCross 8 7 4 half_9_05_φ2) (81190534377529/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (376594730907/5000000000000 : ℝ)) half_9_05_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6 half_8_05
    (by simpa only [half_9_05_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_05_hx3)
  exact h.weaken (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_05_hx1 : SourcePowerBound (powerBoxCross 8 8 2 half_9_05_φ1) (12452780542531/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (453654119187/5000000000000 : ℝ)) half_9_05_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_7_05 half_9_04
    (by simpa only [half_9_05_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_05_hx2)
  exact h.weaken (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_05 : AdmissibleExponent 8 18 (114600741936413/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 7) (ψ := (998566506411/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_8_05
    (by simpa only [half_9_05_φ1] using half_9_05_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_05_φ1, half_9_05_φ2, half_9_05_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_7_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (883076783211/10000000000000 : ℝ)

private def half_7_06_φ2 : Fin 2 → ℝ := Fin.snoc half_7_06_φ1 (734664317439/10000000000000 : ℝ)

private def half_7_06_φ3 : Fin 3 → ℝ := Fin.snoc half_7_06_φ2 (1032644271/39062500000 : ℝ)

private theorem half_7_06_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_7_06_φ3) (35237970642727/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_06_φ3 (by norm_num [half_7_06_φ1, half_7_06_φ2, half_7_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_06_φ1, half_7_06_φ2, half_7_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_06_φ1, half_7_06_φ2, half_7_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_7_06_φ1, half_7_06_φ2, half_7_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_7_06_hF1 : SourcePowerBound (paddedMoment 8 0 1 8 half_7_06_φ3) (13412656880909/5000000000000 : ℝ) := by
  have h := padded_second_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_06_φ3 (by norm_num [half_7_06_φ1, half_7_06_φ2, half_7_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_06_φ1, half_7_06_φ2, half_7_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_06_φ1, half_7_06_φ2, half_7_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_7_06_φ1, half_7_06_φ2, half_7_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_7_06_hx3 : SourcePowerBound (powerBoxCross 8 4 8 half_7_06_φ3) (2658460635909/500000000000 : ℝ) := by
  have h := full_B_cross_power (k := 8) (s := 4) (r := 1) (v := 2) (t := 7) (D := 8)
    (a := (5/14 : ℝ)) (b := (1/14 : ℝ)) (c := (4/7 : ℝ))
    (by norm_num) half_7_06_φ3 (by norm_num [half_7_06_φ1, half_7_06_φ2, half_7_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_06_φ1, half_7_06_φ2, half_7_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_7_06_hF1 half_7_06_hF2 half_7_05
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_7_06_φ1, half_7_06_φ2, half_7_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_06_hx2 : SourcePowerBound (powerBoxCross 8 5 4 half_7_06_φ2) (60584895861851/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 5) (u := 3) (t := 6)
    (D := 4) (ψ := (1032644271/39062500000 : ℝ)) half_7_06_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_7_06_φ1, half_7_06_φ2, half_7_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_06_φ1, half_7_06_φ2, half_7_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_7_06_φ1, half_7_06_φ2, half_7_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_4 SeedCompletionEven8SecondSeeds.degree8_half_6
    (by simpa only [half_7_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_7_06_hx3)
  exact h.weaken (by norm_num [half_7_06_φ1, half_7_06_φ2, half_7_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_06_hx1 : SourcePowerBound (powerBoxCross 8 6 2 half_7_06_φ1) (73394685670219/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 6) (u := 4) (t := 7)
    (D := 2) (ψ := (734664317439/10000000000000 : ℝ)) half_7_06_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_7_06_φ1, half_7_06_φ2, half_7_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_06_φ1, half_7_06_φ2, half_7_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_7_06_φ1, half_7_06_φ2, half_7_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_5 half_7_05
    (by simpa only [half_7_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_7_06_hx2)
  exact h.weaken (by norm_num [half_7_06_φ1, half_7_06_φ2, half_7_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_06 : AdmissibleExponent 8 14 (4155426514277/500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 5) (ψ := (883076783211/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6
    (by simpa only [half_7_06_φ1] using half_7_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_7_06_φ1, half_7_06_φ2, half_7_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_8_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (936820078307/10000000000000 : ℝ)

private def half_8_06_φ2 : Fin 2 → ℝ := Fin.snoc half_8_06_φ1 (414119857923/5000000000000 : ℝ)

private def half_8_06_φ3 : Fin 3 → ℝ := Fin.snoc half_8_06_φ2 (69813917737/1250000000000 : ℝ)

private theorem half_8_06_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_8_06_φ3) (61205006142971/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_06_φ3 (by norm_num [half_8_06_φ1, half_8_06_φ2, half_8_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_06_φ1, half_8_06_φ2, half_8_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_06_φ1, half_8_06_φ2, half_8_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_06_φ1, half_8_06_φ2, half_8_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_06_hx3 : SourcePowerBound (powerBoxCross 8 5 8 half_8_06_φ3) (3017937306437/500000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 5) (r := 2) (v := 6) (w := 7) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_8_06_φ3 (by norm_num [half_8_06_φ1, half_8_06_φ2, half_8_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_06_φ1, half_8_06_φ2, half_8_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_8_06_hF2 SeedCompletionEven8SecondSeeds.degree8_half_6 half_7_06
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_8_06_φ1, half_8_06_φ2, half_8_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_06_hx2 : SourcePowerBound (powerBoxCross 8 6 4 half_8_06_φ2) (70734653698229/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 6) (u := 4) (t := 7)
    (D := 4) (ψ := (69813917737/1250000000000 : ℝ)) half_8_06_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_06_φ1, half_8_06_φ2, half_8_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_06_φ1, half_8_06_φ2, half_8_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_06_φ1, half_8_06_φ2, half_8_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_5 half_7_06
    (by simpa only [half_8_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_8_06_hx3)
  exact h.weaken (by norm_num [half_8_06_φ1, half_8_06_φ2, half_8_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_06_hx1 : SourcePowerBound (powerBoxCross 8 7 2 half_8_06_φ1) (21564894094711/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 7) (u := 5) (t := 8)
    (D := 2) (ψ := (414119857923/5000000000000 : ℝ)) half_8_06_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_06_φ1, half_8_06_φ2, half_8_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_06_φ1, half_8_06_φ2, half_8_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_06_φ1, half_8_06_φ2, half_8_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6 half_8_05
    (by simpa only [half_8_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_8_06_hx2)
  exact h.weaken (by norm_num [half_8_06_φ1, half_8_06_φ2, half_8_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_06 : AdmissibleExponent 8 16 (19687647479367/2000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 6) (ψ := (936820078307/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_7_06
    (by simpa only [half_8_06_φ1] using half_8_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_8_06_φ1, half_8_06_φ2, half_8_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_06_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (994107516931/10000000000000 : ℝ)

private def half_9_06_φ2 : Fin 2 → ℝ := Fin.snoc half_9_06_φ1 (36249454527/400000000000 : ℝ)

private def half_9_06_φ3 : Fin 3 → ℝ := Fin.snoc half_9_06_φ2 (750822804377/10000000000000 : ℝ)

private theorem half_9_06_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_9_06_φ3) (54325499625857/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_06_φ3 (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_06_hx3 : SourcePowerBound (powerBoxCross 8 6 8 half_9_06_φ3) (33918419897081/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 6) (r := 2) (v := 8) (w := 8) (D := 8)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_9_06_φ3 (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_06_hF2 half_8_06 half_8_06
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_06_hx2 : SourcePowerBound (powerBoxCross 8 7 4 half_9_06_φ2) (81262535338927/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (750822804377/10000000000000 : ℝ)) half_9_06_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6 half_8_06
    (by simpa only [half_9_06_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_06_hx3)
  exact h.weaken (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_06_hx1 : SourcePowerBound (powerBoxCross 8 8 2 half_9_06_φ1) (99646525738807/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (36249454527/400000000000 : ℝ)) half_9_06_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_7_06 half_9_05
    (by simpa only [half_9_06_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_06_hx2)
  exact h.weaken (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_06 : AdmissibleExponent 8 18 (28639534623193/2500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 7) (ψ := (994107516931/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_8_06
    (by simpa only [half_9_06_φ1] using half_9_06_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_06_φ1, half_9_06_φ2, half_9_06_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_7_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (220686943507/2500000000000 : ℝ)

private def half_7_07_φ2 : Fin 2 → ℝ := Fin.snoc half_7_07_φ1 (734516086513/10000000000000 : ℝ)

private def half_7_07_φ3 : Fin 3 → ℝ := Fin.snoc half_7_07_φ2 (131859365201/5000000000000 : ℝ)

private theorem half_7_07_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_7_07_φ3) (70499365590197/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_07_φ3 (by norm_num [half_7_07_φ1, half_7_07_φ2, half_7_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_07_φ1, half_7_07_φ2, half_7_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_07_φ1, half_7_07_φ2, half_7_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_7_07_φ1, half_7_07_φ2, half_7_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_7_07_hF1 : SourcePowerBound (paddedMoment 8 0 1 8 half_7_07_φ3) (26833121863399/10000000000000 : ℝ) := by
  have h := padded_second_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_07_φ3 (by norm_num [half_7_07_φ1, half_7_07_φ2, half_7_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_07_φ1, half_7_07_φ2, half_7_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_07_φ1, half_7_07_φ2, half_7_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_7_07_φ1, half_7_07_φ2, half_7_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_7_07_hx3 : SourcePowerBound (powerBoxCross 8 4 8 half_7_07_φ3) (53176618449339/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 8) (s := 4) (r := 1) (v := 2) (t := 7) (D := 8)
    (a := (5/14 : ℝ)) (b := (1/14 : ℝ)) (c := (4/7 : ℝ))
    (by norm_num) half_7_07_φ3 (by norm_num [half_7_07_φ1, half_7_07_φ2, half_7_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_07_φ1, half_7_07_φ2, half_7_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_7_07_hF1 half_7_07_hF2 half_7_06
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_7_07_φ1, half_7_07_φ2, half_7_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_07_hx2 : SourcePowerBound (powerBoxCross 8 5 4 half_7_07_φ2) (605896714931/100000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 5) (u := 3) (t := 6)
    (D := 4) (ψ := (131859365201/5000000000000 : ℝ)) half_7_07_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_7_07_φ1, half_7_07_φ2, half_7_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_07_φ1, half_7_07_φ2, half_7_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_7_07_φ1, half_7_07_φ2, half_7_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_4 SeedCompletionEven8SecondSeeds.degree8_half_6
    (by simpa only [half_7_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_7_07_hx3)
  exact h.weaken (by norm_num [half_7_07_φ1, half_7_07_φ2, half_7_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_07_hx1 : SourcePowerBound (powerBoxCross 8 6 2 half_7_07_φ1) (18349153140979/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 6) (u := 4) (t := 7)
    (D := 2) (ψ := (734516086513/10000000000000 : ℝ)) half_7_07_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_7_07_φ1, half_7_07_φ2, half_7_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_07_φ1, half_7_07_φ2, half_7_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_7_07_φ1, half_7_07_φ2, half_7_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_5 half_7_06
    (by simpa only [half_7_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_7_07_hx2)
  exact h.weaken (by norm_num [half_7_07_φ1, half_7_07_φ2, half_7_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_07 : AdmissibleExponent 8 14 (5194177379889/625000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 5) (ψ := (220686943507/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6
    (by simpa only [half_7_07_φ1] using half_7_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_7_07_φ1, half_7_07_φ2, half_7_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_8_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (58500548439/625000000000 : ℝ)

private def half_8_07_φ2 : Fin 2 → ℝ := Fin.snoc half_8_07_φ1 (828073417521/10000000000000 : ℝ)

private def half_8_07_φ3 : Fin 3 → ℝ := Fin.snoc half_8_07_φ2 (55821097107/1000000000000 : ℝ)

private theorem half_8_07_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_8_07_φ3) (12246368712817/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_07_φ3 (by norm_num [half_8_07_φ1, half_8_07_φ2, half_8_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_07_φ1, half_8_07_φ2, half_8_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_07_φ1, half_8_07_φ2, half_8_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_07_φ1, half_8_07_φ2, half_8_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_07_hx3 : SourcePowerBound (powerBoxCross 8 5 8 half_8_07_φ3) (30186153522701/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 5) (r := 2) (v := 6) (w := 7) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_8_07_φ3 (by norm_num [half_8_07_φ1, half_8_07_φ2, half_8_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_07_φ1, half_8_07_φ2, half_8_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_8_07_hF2 SeedCompletionEven8SecondSeeds.degree8_half_6 half_7_07
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_8_07_φ1, half_8_07_φ2, half_8_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_07_hx2 : SourcePowerBound (powerBoxCross 8 6 4 half_8_07_φ2) (14149373920219/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 6) (u := 4) (t := 7)
    (D := 4) (ψ := (55821097107/1000000000000 : ℝ)) half_8_07_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_07_φ1, half_8_07_φ2, half_8_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_07_φ1, half_8_07_φ2, half_8_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_07_φ1, half_8_07_φ2, half_8_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_5 half_7_07
    (by simpa only [half_8_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_8_07_hx3)
  exact h.weaken (by norm_num [half_8_07_φ1, half_8_07_φ2, half_8_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_07_hx1 : SourcePowerBound (powerBoxCross 8 7 2 half_8_07_φ1) (2156599347067/250000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 7) (u := 5) (t := 8)
    (D := 2) (ψ := (828073417521/10000000000000 : ℝ)) half_8_07_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_07_φ1, half_8_07_φ2, half_8_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_07_φ1, half_8_07_φ2, half_8_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_07_φ1, half_8_07_φ2, half_8_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6 half_8_06
    (by simpa only [half_8_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_8_07_hx2)
  exact h.weaken (by norm_num [half_8_07_φ1, half_8_07_φ2, half_8_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_07 : AdmissibleExponent 8 16 (12304010994749/1250000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 6) (ψ := (58500548439/625000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_7_07
    (by simpa only [half_8_07_φ1] using half_8_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_8_07_φ1, half_8_07_φ2, half_8_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_07_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (124021777089/1250000000000 : ℝ)

private def half_9_07_φ2 : Fin 2 → ℝ := Fin.snoc half_9_07_φ1 (905810121037/10000000000000 : ℝ)

private def half_9_07_φ3 : Fin 3 → ℝ := Fin.snoc half_9_07_φ2 (374948131791/5000000000000 : ℝ)

private theorem half_9_07_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_9_07_φ3) (54394507372049/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_07_φ3 (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_07_hx3 : SourcePowerBound (powerBoxCross 8 6 8 half_9_07_φ3) (67874961592571/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 6) (r := 2) (v := 8) (w := 8) (D := 8)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_9_07_φ3 (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_07_hF2 half_8_07 half_8_07
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_07_hx2 : SourcePowerBound (powerBoxCross 8 7 4 half_9_07_φ2) (81293880979051/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (374948131791/5000000000000 : ℝ)) half_9_07_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6 half_8_07
    (by simpa only [half_9_07_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_07_hx3)
  exact h.weaken (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_07_hx1 : SourcePowerBound (powerBoxCross 8 8 2 half_9_07_φ1) (6228630262363/625000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (905810121037/10000000000000 : ℝ)) half_9_07_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_7_07 half_9_06
    (by simpa only [half_9_07_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_07_hx2)
  exact h.weaken (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_07 : AdmissibleExponent 8 18 (14317587181061/1250000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 7) (ψ := (124021777089/1250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_8_07
    (by simpa only [half_9_07_φ1] using half_9_07_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_07_φ1, half_9_07_φ2, half_9_07_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_7_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (882638023097/10000000000000 : ℝ)

private def half_7_08_φ2 : Fin 2 → ℝ := Fin.snoc half_7_08_φ1 (367233317539/5000000000000 : ℝ)

private def half_7_08_φ3 : Fin 3 → ℝ := Fin.snoc half_7_08_φ2 (16469113703/625000000000 : ℝ)

private theorem half_7_08_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_7_08_φ3) (70507179974117/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_08_φ3 (by norm_num [half_7_08_φ1, half_7_08_φ2, half_7_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_08_φ1, half_7_08_φ2, half_7_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_08_φ1, half_7_08_φ2, half_7_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_7_08_φ1, half_7_08_φ2, half_7_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_7_08_hF1 : SourcePowerBound (paddedMoment 8 0 1 8 half_7_08_φ3) (26835726658039/10000000000000 : ℝ) := by
  have h := padded_second_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_08_φ3 (by norm_num [half_7_08_φ1, half_7_08_φ2, half_7_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_08_φ1, half_7_08_φ2, half_7_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_08_φ1, half_7_08_φ2, half_7_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_7_08_φ1, half_7_08_φ2, half_7_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_7_08_hx3 : SourcePowerBound (powerBoxCross 8 4 8 half_7_08_φ3) (53179088967271/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 8) (s := 4) (r := 1) (v := 2) (t := 7) (D := 8)
    (a := (5/14 : ℝ)) (b := (1/14 : ℝ)) (c := (4/7 : ℝ))
    (by norm_num) half_7_08_φ3 (by norm_num [half_7_08_φ1, half_7_08_φ2, half_7_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_08_φ1, half_7_08_φ2, half_7_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_7_08_hF1 half_7_08_hF2 half_7_07
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_7_08_φ1, half_7_08_φ2, half_7_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_08_hx2 : SourcePowerBound (powerBoxCross 8 5 4 half_7_08_φ2) (3029563228463/500000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 5) (u := 3) (t := 6)
    (D := 4) (ψ := (16469113703/625000000000 : ℝ)) half_7_08_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_7_08_φ1, half_7_08_φ2, half_7_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_08_φ1, half_7_08_φ2, half_7_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_7_08_φ1, half_7_08_φ2, half_7_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_4 SeedCompletionEven8SecondSeeds.degree8_half_6
    (by simpa only [half_7_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_7_08_hx3)
  exact h.weaken (by norm_num [half_7_08_φ1, half_7_08_φ2, half_7_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_08_hx1 : SourcePowerBound (powerBoxCross 8 6 2 half_7_08_φ1) (36698627668697/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 6) (u := 4) (t := 7)
    (D := 2) (ψ := (367233317539/5000000000000 : ℝ)) half_7_08_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_7_08_φ1, half_7_08_φ2, half_7_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_08_φ1, half_7_08_φ2, half_7_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_7_08_φ1, half_7_08_φ2, half_7_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_5 half_7_07
    (by simpa only [half_7_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_7_08_hx2)
  exact h.weaken (by norm_num [half_7_08_φ1, half_7_08_φ2, half_7_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_08 : AdmissibleExponent 8 14 (83106273591461/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 5) (ψ := (882638023097/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6
    (by simpa only [half_7_08_φ1] using half_7_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_7_08_φ1, half_7_08_φ2, half_7_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_8_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (23392686551/250000000000 : ℝ)

private def half_8_08_φ2 : Fin 2 → ℝ := Fin.snoc half_8_08_φ1 (16560324547/200000000000 : ℝ)

private def half_8_08_φ3 : Fin 3 → ℝ := Fin.snoc half_8_08_φ2 (139526014951/2500000000000 : ℝ)

private theorem half_8_08_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_8_08_φ3) (30620808633463/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_08_φ3 (by norm_num [half_8_08_φ1, half_8_08_φ2, half_8_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_08_φ1, half_8_08_φ2, half_8_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_08_φ1, half_8_08_φ2, half_8_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_08_φ1, half_8_08_φ2, half_8_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_08_hx3 : SourcePowerBound (powerBoxCross 8 5 8 half_8_08_φ3) (60377265512507/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 5) (r := 2) (v := 6) (w := 7) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_8_08_φ3 (by norm_num [half_8_08_φ1, half_8_08_φ2, half_8_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_08_φ1, half_8_08_φ2, half_8_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_8_08_hF2 SeedCompletionEven8SecondSeeds.degree8_half_6 half_7_08
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_8_08_φ1, half_8_08_φ2, half_8_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_08_hx2 : SourcePowerBound (powerBoxCross 8 6 4 half_8_08_φ2) (8843922466841/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 6) (u := 4) (t := 7)
    (D := 4) (ψ := (139526014951/2500000000000 : ℝ)) half_8_08_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_08_φ1, half_8_08_φ2, half_8_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_08_φ1, half_8_08_φ2, half_8_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_08_φ1, half_8_08_φ2, half_8_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_5 half_7_08
    (by simpa only [half_8_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_8_08_hx3)
  exact h.weaken (by norm_num [half_8_08_φ1, half_8_08_φ2, half_8_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_08_hx1 : SourcePowerBound (powerBoxCross 8 7 2 half_8_08_φ1) (43132832509661/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 7) (u := 5) (t := 8)
    (D := 2) (ψ := (16560324547/200000000000 : ℝ)) half_8_08_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_08_φ1, half_8_08_φ2, half_8_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_08_φ1, half_8_08_φ2, half_8_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_08_φ1, half_8_08_φ2, half_8_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6 half_8_07
    (by simpa only [half_8_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_8_08_hx2)
  exact h.weaken (by norm_num [half_8_08_φ1, half_8_08_φ2, half_8_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_08 : AdmissibleExponent 8 16 (49214931012921/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 6) (ψ := (23392686551/250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_7_08
    (by simpa only [half_8_08_φ1] using half_8_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_8_08_φ1, half_8_08_φ2, half_8_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_08_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (1936248741/19531250000 : ℝ)

private def half_9_08_φ2 : Fin 2 → ℝ := Fin.snoc half_9_08_φ1 (905644170273/10000000000000 : ℝ)

private def half_9_08_φ3 : Fin 3 → ℝ := Fin.snoc half_9_08_φ2 (749537870597/10000000000000 : ℝ)

private theorem half_9_08_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_9_08_φ3) (27211315339249/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_08_φ3 (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_08_hx3 : SourcePowerBound (powerBoxCross 8 6 8 half_9_08_φ3) (2715626054121/400000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 6) (r := 2) (v := 8) (w := 8) (D := 8)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_9_08_φ3 (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_08_hF2 half_8_08 half_8_08
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_08_hx2 : SourcePowerBound (powerBoxCross 8 7 4 half_9_08_φ2) (81307112873203/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (749537870597/10000000000000 : ℝ)) half_9_08_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6 half_8_08
    (by simpa only [half_9_08_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_08_hx3)
  exact h.weaken (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_08_hx1 : SourcePowerBound (powerBoxCross 8 8 2 half_9_08_φ1) (49831642462157/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (905644170273/10000000000000 : ℝ)) half_9_08_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_7_08 half_9_07
    (by simpa only [half_9_08_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_08_hx2)
  exact h.weaken (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_08 : AdmissibleExponent 8 18 (57266837627597/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 7) (ψ := (1936248741/19531250000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_8_08
    (by simpa only [half_9_08_φ1] using half_9_08_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_08_φ1, half_9_08_φ2, half_9_08_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_7_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (176520282323/2000000000000 : ℝ)

private def half_7_09_φ2 : Fin 2 → ℝ := Fin.snoc half_7_09_φ1 (367225069109/5000000000000 : ℝ)

private def half_7_09_φ3 : Fin 3 → ℝ := Fin.snoc half_7_09_φ2 (26343479271/1000000000000 : ℝ)

private theorem half_7_09_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_7_09_φ3) (70509786806597/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_09_φ3 (by norm_num [half_7_09_φ1, half_7_09_φ2, half_7_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_09_φ1, half_7_09_φ2, half_7_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_09_φ1, half_7_09_φ2, half_7_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_7_09_φ1, half_7_09_φ2, half_7_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_7_09_hF1 : SourcePowerBound (paddedMoment 8 0 1 8 half_7_09_φ3) (26836595602199/10000000000000 : ℝ) := by
  have h := padded_second_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_09_φ3 (by norm_num [half_7_09_φ1, half_7_09_φ2, half_7_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_09_φ1, half_7_09_φ2, half_7_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_09_φ1, half_7_09_φ2, half_7_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_7_09_φ1, half_7_09_φ2, half_7_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_7_09_hx3 : SourcePowerBound (powerBoxCross 8 4 8 half_7_09_φ3) (5317991311247/1000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 8) (s := 4) (r := 1) (v := 2) (t := 7) (D := 8)
    (a := (5/14 : ℝ)) (b := (1/14 : ℝ)) (c := (4/7 : ℝ))
    (by norm_num) half_7_09_φ3 (by norm_num [half_7_09_φ1, half_7_09_φ2, half_7_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_09_φ1, half_7_09_φ2, half_7_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_7_09_hF1 half_7_09_hF2 half_7_08
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_7_09_φ1, half_7_09_φ2, half_7_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_09_hx2 : SourcePowerBound (powerBoxCross 8 5 4 half_7_09_φ2) (60591796000997/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 5) (u := 3) (t := 6)
    (D := 4) (ψ := (26343479271/1000000000000 : ℝ)) half_7_09_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_7_09_φ1, half_7_09_φ2, half_7_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_09_φ1, half_7_09_φ2, half_7_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_7_09_φ1, half_7_09_φ2, half_7_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_4 SeedCompletionEven8SecondSeeds.degree8_half_6
    (by simpa only [half_7_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_7_09_hx3)
  exact h.weaken (by norm_num [half_7_09_φ1, half_7_09_φ2, half_7_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_09_hx1 : SourcePowerBound (powerBoxCross 8 6 2 half_7_09_φ1) (9174683719783/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 6) (u := 4) (t := 7)
    (D := 2) (ψ := (367225069109/5000000000000 : ℝ)) half_7_09_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_7_09_φ1, half_7_09_φ2, half_7_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_09_φ1, half_7_09_φ2, half_7_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_7_09_φ1, half_7_09_φ2, half_7_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_5 half_7_08
    (by simpa only [half_7_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_7_09_hx2)
  exact h.weaken (by norm_num [half_7_09_φ1, half_7_09_φ2, half_7_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_09 : AdmissibleExponent 8 14 (83106085286029/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 5) (ψ := (176520282323/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6
    (by simpa only [half_7_09_φ1] using half_7_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_7_09_φ1, half_7_09_φ2, half_7_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_8_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (233899230959/2500000000000 : ℝ)

private def half_8_09_φ2 : Fin 2 → ℝ := Fin.snoc half_8_09_φ1 (165599318011/2000000000000 : ℝ)

private def half_8_09_φ3 : Fin 3 → ℝ := Fin.snoc half_8_09_φ2 (22322648149/400000000000 : ℝ)

private theorem half_8_09_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_8_09_φ3) (3827821620629/625000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_09_φ3 (by norm_num [half_8_09_φ1, half_8_09_φ2, half_8_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_09_φ1, half_8_09_φ2, half_8_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_09_φ1, half_8_09_φ2, half_8_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_09_φ1, half_8_09_φ2, half_8_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_09_hx3 : SourcePowerBound (powerBoxCross 8 5 8 half_8_09_φ3) (60379061642241/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 5) (r := 2) (v := 6) (w := 7) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_8_09_φ3 (by norm_num [half_8_09_φ1, half_8_09_φ2, half_8_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_09_φ1, half_8_09_φ2, half_8_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_8_09_hF2 SeedCompletionEven8SecondSeeds.degree8_half_6 half_7_09
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_8_09_φ1, half_8_09_φ2, half_8_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_09_hx2 : SourcePowerBound (powerBoxCross 8 6 4 half_8_09_φ2) (35376513216757/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 6) (u := 4) (t := 7)
    (D := 4) (ψ := (22322648149/400000000000 : ℝ)) half_8_09_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_09_φ1, half_8_09_φ2, half_8_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_09_φ1, half_8_09_φ2, half_8_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_09_φ1, half_8_09_φ2, half_8_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_5 half_7_09
    (by simpa only [half_8_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_8_09_hx3)
  exact h.weaken (by norm_num [half_8_09_φ1, half_8_09_φ2, half_8_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_09_hx1 : SourcePowerBound (powerBoxCross 8 7 2 half_8_09_φ1) (43133151217653/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 7) (u := 5) (t := 8)
    (D := 2) (ψ := (165599318011/2000000000000 : ℝ)) half_8_09_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_09_φ1, half_8_09_φ2, half_8_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_09_φ1, half_8_09_φ2, half_8_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_09_φ1, half_8_09_φ2, half_8_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6 half_8_08
    (by simpa only [half_8_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_8_09_hx2)
  exact h.weaken (by norm_num [half_8_09_φ1, half_8_09_φ2, half_8_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_09 : AdmissibleExponent 8 16 (49214531222587/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 6) (ψ := (233899230959/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_7_09
    (by simpa only [half_8_09_φ1] using half_8_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_8_09_φ1, half_8_09_φ2, half_8_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_09_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (247755877199/2500000000000 : ℝ)

private def half_9_09_φ2 : Fin 2 → ℝ := Fin.snoc half_9_09_φ1 (36223223143/400000000000 : ℝ)

private def half_9_09_φ3 : Fin 3 → ℝ := Fin.snoc half_9_09_φ2 (374700300077/5000000000000 : ℝ)

private theorem half_9_09_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_9_09_φ3) (2177356062479/400000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_09_φ3 (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_09_hx3 : SourcePowerBound (powerBoxCross 8 6 8 half_9_09_φ3) (33948495088989/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 6) (r := 2) (v := 8) (w := 8) (D := 8)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_9_09_φ3 (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_09_hF2 half_8_09 half_8_09
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_09_hx2 : SourcePowerBound (powerBoxCross 8 7 4 half_9_09_φ2) (10164070899893/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (374700300077/5000000000000 : ℝ)) half_9_09_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6 half_8_09
    (by simpa only [half_9_09_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_09_hx3)
  exact h.weaken (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_09_hx1 : SourcePowerBound (powerBoxCross 8 8 2 half_9_09_φ1) (49832767235393/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (36223223143/400000000000 : ℝ)) half_9_09_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_7_09 half_9_08
    (by simpa only [half_9_09_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_09_hx2)
  exact h.weaken (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_09 : AdmissibleExponent 8 18 (57265443551363/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 7) (ψ := (247755877199/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_8_09
    (by simpa only [half_9_09_φ1] using half_9_09_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_09_φ1, half_9_09_φ2, half_9_09_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_7_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (882589198419/10000000000000 : ℝ)

private def half_7_10_φ2 : Fin 2 → ℝ := Fin.snoc half_7_10_φ1 (367222317493/5000000000000 : ℝ)

private def half_7_10_φ3 : Fin 3 → ℝ := Fin.snoc half_7_10_φ2 (263411098781/10000000000000 : ℝ)

private theorem half_7_10_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_7_10_φ3) (35255328212047/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_10_φ3 (by norm_num [half_7_10_φ1, half_7_10_φ2, half_7_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_10_φ1, half_7_10_φ2, half_7_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_10_φ1, half_7_10_φ2, half_7_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_7_10_φ1, half_7_10_φ2, half_7_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_7_10_hF1 : SourcePowerBound (paddedMoment 8 0 1 8 half_7_10_φ3) (13418442737349/5000000000000 : ℝ) := by
  have h := padded_second_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_10_φ3 (by norm_num [half_7_10_φ1, half_7_10_φ2, half_7_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_10_φ1, half_7_10_φ2, half_7_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_10_φ1, half_7_10_φ2, half_7_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_7_10_φ1, half_7_10_φ2, half_7_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_7_10_hx3 : SourcePowerBound (powerBoxCross 8 4 8 half_7_10_φ3) (6647523504981/1250000000000 : ℝ) := by
  have h := full_B_cross_power (k := 8) (s := 4) (r := 1) (v := 2) (t := 7) (D := 8)
    (a := (5/14 : ℝ)) (b := (1/14 : ℝ)) (c := (4/7 : ℝ))
    (by norm_num) half_7_10_φ3 (by norm_num [half_7_10_φ1, half_7_10_φ2, half_7_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_10_φ1, half_7_10_φ2, half_7_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_7_10_hF1 half_7_10_hF2 half_7_09
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_7_10_φ1, half_7_10_φ2, half_7_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_10_hx2 : SourcePowerBound (powerBoxCross 8 5 4 half_7_10_φ2) (60591973281161/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 5) (u := 3) (t := 6)
    (D := 4) (ψ := (263411098781/10000000000000 : ℝ)) half_7_10_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_7_10_φ1, half_7_10_φ2, half_7_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_10_φ1, half_7_10_φ2, half_7_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_7_10_φ1, half_7_10_φ2, half_7_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_4 SeedCompletionEven8SecondSeeds.degree8_half_6
    (by simpa only [half_7_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_7_10_hx3)
  exact h.weaken (by norm_num [half_7_10_φ1, half_7_10_φ2, half_7_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_10_hx1 : SourcePowerBound (powerBoxCross 8 6 2 half_7_10_φ1) (73397541286749/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 6) (u := 4) (t := 7)
    (D := 2) (ψ := (367222317493/5000000000000 : ℝ)) half_7_10_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_7_10_φ1, half_7_10_φ2, half_7_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_10_φ1, half_7_10_φ2, half_7_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_7_10_φ1, half_7_10_φ2, half_7_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_5 half_7_09
    (by simpa only [half_7_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_7_10_hx2)
  exact h.weaken (by norm_num [half_7_10_φ1, half_7_10_φ2, half_7_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_10 : AdmissibleExponent 8 14 (41553011234679/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 5) (ψ := (882589198419/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6
    (by simpa only [half_7_10_φ1] using half_7_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_7_10_φ1, half_7_10_φ2, half_7_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_8_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (58472298447/625000000000 : ℝ)

private def half_8_10_φ2 : Fin 2 → ℝ := Fin.snoc half_8_10_φ1 (413994928357/5000000000000 : ℝ)

private def half_8_10_φ3 : Fin 3 → ℝ := Fin.snoc half_8_10_φ2 (111610571919/2000000000000 : ℝ)

private theorem half_8_10_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_8_10_φ3) (61246410679319/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_10_φ3 (by norm_num [half_8_10_φ1, half_8_10_φ2, half_8_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_10_φ1, half_8_10_φ2, half_8_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_10_φ1, half_8_10_φ2, half_8_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_10_φ1, half_8_10_φ2, half_8_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_10_hx3 : SourcePowerBound (powerBoxCross 8 5 8 half_8_10_φ3) (60379707208487/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 5) (r := 2) (v := 6) (w := 7) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_8_10_φ3 (by norm_num [half_8_10_φ1, half_8_10_φ2, half_8_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_10_φ1, half_8_10_φ2, half_8_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_8_10_hF2 SeedCompletionEven8SecondSeeds.degree8_half_6 half_7_10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_8_10_φ1, half_8_10_φ2, half_8_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_10_hx2 : SourcePowerBound (powerBoxCross 8 6 4 half_8_10_φ2) (70753622194889/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 6) (u := 4) (t := 7)
    (D := 4) (ψ := (111610571919/2000000000000 : ℝ)) half_8_10_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_10_φ1, half_8_10_φ2, half_8_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_10_φ1, half_8_10_φ2, half_8_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_10_φ1, half_8_10_φ2, half_8_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_5 half_7_10
    (by simpa only [half_8_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_8_10_hx3)
  exact h.weaken (by norm_num [half_8_10_φ1, half_8_10_φ2, half_8_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_10_hx1 : SourcePowerBound (powerBoxCross 8 7 2 half_8_10_φ1) (17253307801361/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 7) (u := 5) (t := 8)
    (D := 2) (ψ := (413994928357/5000000000000 : ℝ)) half_8_10_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_10_φ1, half_8_10_φ2, half_8_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_10_φ1, half_8_10_φ2, half_8_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_10_φ1, half_8_10_φ2, half_8_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6 half_8_09
    (by simpa only [half_8_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_8_10_hx2)
  exact h.weaken (by norm_num [half_8_10_φ1, half_8_10_φ2, half_8_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_10 : AdmissibleExponent 8 16 (98428777083781/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 6) (ψ := (58472298447/625000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_7_10
    (by simpa only [half_8_10_φ1] using half_8_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_8_10_φ1, half_8_10_φ2, half_8_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_10_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (990887576037/10000000000000 : ℝ)

private def half_9_10_φ2 : Fin 2 → ℝ := Fin.snoc half_9_10_φ1 (36222260383/400000000000 : ℝ)

private def half_9_10_φ3 : Fin 3 → ℝ := Fin.snoc half_9_10_φ2 (29973938181/400000000000 : ℝ)

private theorem half_9_10_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_9_10_φ3) (54438356657123/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_10_φ3 (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_10_hx3 : SourcePowerBound (powerBoxCross 8 6 8 half_9_10_φ3) (33949756333193/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 6) (r := 2) (v := 8) (w := 8) (D := 8)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_9_10_φ3 (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_10_hF2 half_8_10 half_8_10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_10_hx2 : SourcePowerBound (powerBoxCross 8 7 4 half_9_10_φ2) (40657386733801/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (29973938181/400000000000 : ℝ)) half_9_10_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6 half_8_10
    (by simpa only [half_9_10_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_10_hx3)
  exact h.weaken (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_10_hx1 : SourcePowerBound (powerBoxCross 8 8 2 half_9_10_φ1) (99666479426143/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (36222260383/400000000000 : ℝ)) half_9_10_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_7_10 half_9_09
    (by simpa only [half_9_10_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_10_hx2)
  exact h.weaken (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_10 : AdmissibleExponent 8 18 (57264896533349/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 7) (ψ := (990887576037/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_8_10
    (by simpa only [half_9_10_φ1] using half_9_10_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_10_φ1, half_9_10_φ2, half_9_10_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_7_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (441292562109/5000000000000 : ℝ)

private def half_7_11_φ2 : Fin 2 → ℝ := Fin.snoc half_7_11_φ1 (734442799157/10000000000000 : ℝ)

private def half_7_11_φ3 : Fin 3 → ℝ := Fin.snoc half_7_11_φ2 (32925399337/1250000000000 : ℝ)

private theorem half_7_11_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_7_11_φ3) (70510946520509/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_11_φ3 (by norm_num [half_7_11_φ1, half_7_11_φ2, half_7_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_11_φ1, half_7_11_φ2, half_7_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_11_φ1, half_7_11_φ2, half_7_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_7_11_φ1, half_7_11_φ2, half_7_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_7_11_hF1 : SourcePowerBound (paddedMoment 8 0 1 8 half_7_11_φ3) (26836982173503/10000000000000 : ℝ) := by
  have h := padded_second_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_11_φ3 (by norm_num [half_7_11_φ1, half_7_11_φ2, half_7_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_11_φ1, half_7_11_φ2, half_7_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_11_φ1, half_7_11_φ2, half_7_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_7_11_φ1, half_7_11_φ2, half_7_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_7_11_hx3 : SourcePowerBound (powerBoxCross 8 4 8 half_7_11_φ3) (13295069938259/2500000000000 : ℝ) := by
  have h := full_B_cross_power (k := 8) (s := 4) (r := 1) (v := 2) (t := 7) (D := 8)
    (a := (5/14 : ℝ)) (b := (1/14 : ℝ)) (c := (4/7 : ℝ))
    (by norm_num) half_7_11_φ3 (by norm_num [half_7_11_φ1, half_7_11_φ2, half_7_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_11_φ1, half_7_11_φ2, half_7_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_7_11_hF1 half_7_11_hF2 half_7_10
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_7_11_φ1, half_7_11_φ2, half_7_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_11_hx2 : SourcePowerBound (powerBoxCross 8 5 4 half_7_11_φ2) (15148008105021/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 5) (u := 3) (t := 6)
    (D := 4) (ψ := (32925399337/1250000000000 : ℝ)) half_7_11_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_7_11_φ1, half_7_11_φ2, half_7_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_11_φ1, half_7_11_φ2, half_7_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_7_11_φ1, half_7_11_φ2, half_7_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_4 SeedCompletionEven8SecondSeeds.degree8_half_6
    (by simpa only [half_7_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_7_11_hx3)
  exact h.weaken (by norm_num [half_7_11_φ1, half_7_11_φ2, half_7_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_11_hx1 : SourcePowerBound (powerBoxCross 8 6 2 half_7_11_φ1) (36698782573973/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 6) (u := 4) (t := 7)
    (D := 2) (ψ := (734442799157/10000000000000 : ℝ)) half_7_11_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_7_11_φ1, half_7_11_φ2, half_7_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_11_φ1, half_7_11_φ2, half_7_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_7_11_φ1, half_7_11_φ2, half_7_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_5 half_7_10
    (by simpa only [half_7_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_7_11_hx2)
  exact h.weaken (by norm_num [half_7_11_φ1, half_7_11_φ2, half_7_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_11 : AdmissibleExponent 8 14 (10388250189293/1250000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 5) (ψ := (441292562109/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6
    (by simpa only [half_7_11_φ1] using half_7_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_7_11_φ1, half_7_11_φ2, half_7_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_8_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (935542312553/10000000000000 : ℝ)

private def half_8_11_φ2 : Fin 2 → ℝ := Fin.snoc half_8_11_φ1 (413993775469/5000000000000 : ℝ)

private def half_8_11_φ3 : Fin 3 → ℝ := Fin.snoc half_8_11_φ2 (139512043597/2500000000000 : ℝ)

private theorem half_8_11_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_8_11_φ3) (61246861204541/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_11_φ3 (by norm_num [half_8_11_φ1, half_8_11_φ2, half_8_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_11_φ1, half_8_11_φ2, half_8_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_11_φ1, half_8_11_φ2, half_8_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_11_φ1, half_8_11_φ2, half_8_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_11_hx3 : SourcePowerBound (powerBoxCross 8 5 8 half_8_11_φ3) (60379937715773/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 5) (r := 2) (v := 6) (w := 7) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_8_11_φ3 (by norm_num [half_8_11_φ1, half_8_11_φ2, half_8_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_11_φ1, half_8_11_φ2, half_8_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_8_11_hF2 SeedCompletionEven8SecondSeeds.degree8_half_6 half_7_11
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_8_11_φ1, half_8_11_φ2, half_8_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_11_hx2 : SourcePowerBound (powerBoxCross 8 6 4 half_8_11_φ2) (70753836102293/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 6) (u := 4) (t := 7)
    (D := 4) (ψ := (139512043597/2500000000000 : ℝ)) half_8_11_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_11_φ1, half_8_11_φ2, half_8_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_11_φ1, half_8_11_φ2, half_8_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_11_φ1, half_8_11_φ2, half_8_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_5 half_7_11
    (by simpa only [half_8_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_8_11_hx3)
  exact h.weaken (by norm_num [half_8_11_φ1, half_8_11_φ2, half_8_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_11_hx1 : SourcePowerBound (powerBoxCross 8 7 2 half_8_11_φ1) (3450665029701/400000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 7) (u := 5) (t := 8)
    (D := 2) (ψ := (413993775469/5000000000000 : ℝ)) half_8_11_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_11_φ1, half_8_11_φ2, half_8_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_11_φ1, half_8_11_φ2, half_8_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_11_φ1, half_8_11_φ2, half_8_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6 half_8_10
    (by simpa only [half_8_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_8_11_hx2)
  exact h.weaken (by norm_num [half_8_11_φ1, half_8_11_φ2, half_8_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_11 : AdmissibleExponent 8 16 (49214337902857/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 6) (ψ := (935542312553/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_7_11
    (by simpa only [half_8_11_φ1] using half_8_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_8_11_φ1, half_8_11_φ2, half_8_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_11_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (495416687149/5000000000000 : ℝ)

private def half_9_11_φ2 : Fin 2 → ℝ := Fin.snoc half_9_11_φ1 (181109497793/2000000000000 : ℝ)

private def half_9_11_φ3 : Fin 3 → ℝ := Fin.snoc half_9_11_φ2 (187332195997/2500000000000 : ℝ)

private theorem half_9_11_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_9_11_φ3) (54440097407729/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_11_φ3 (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_11_hx3 : SourcePowerBound (powerBoxCross 8 6 8 half_9_11_φ3) (67900503920319/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 6) (r := 2) (v := 8) (w := 8) (D := 8)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_9_11_φ3 (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_11_hF2 half_8_11 half_8_11
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_11_hx2 : SourcePowerBound (powerBoxCross 8 7 4 half_9_11_φ2) (81315652293817/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (187332195997/2500000000000 : ℝ)) half_9_11_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6 half_8_11
    (by simpa only [half_9_11_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_11_hx3)
  exact h.weaken (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_11_hx1 : SourcePowerBound (powerBoxCross 8 8 2 half_9_11_φ1) (99666867482391/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (181109497793/2000000000000 : ℝ)) half_9_11_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_7_11 half_9_10
    (by simpa only [half_9_11_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_11_hx2)
  exact h.weaken (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_11 : AdmissibleExponent 8 18 (114529368096861/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 7) (ψ := (495416687149/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_8_11
    (by simpa only [half_9_11_φ1] using half_9_11_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_11_φ1, half_9_11_φ2, half_9_11_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_7_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (55161485319/625000000000 : ℝ)

private def half_7_12_φ2 : Fin 2 → ℝ := Fin.snoc half_7_12_φ1 (734442186741/10000000000000 : ℝ)

private def half_7_12_φ3 : Fin 3 → ℝ := Fin.snoc half_7_12_φ2 (263400557967/10000000000000 : ℝ)

private theorem half_7_12_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_7_12_φ3) (17627760823487/2500000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_12_φ3 (by norm_num [half_7_12_φ1, half_7_12_φ2, half_7_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_12_φ1, half_7_12_φ2, half_7_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_12_φ1, half_7_12_φ2, half_7_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_7_12_φ1, half_7_12_φ2, half_7_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_7_12_hF1 : SourcePowerBound (paddedMoment 8 0 1 8 half_7_12_φ3) (6709253607829/2500000000000 : ℝ) := by
  have h := padded_second_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_12_φ3 (by norm_num [half_7_12_φ1, half_7_12_φ2, half_7_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_12_φ1, half_7_12_φ2, half_7_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_12_φ1, half_7_12_φ2, half_7_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_7_12_φ1, half_7_12_φ2, half_7_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_7_12_hx3 : SourcePowerBound (powerBoxCross 8 4 8 half_7_12_φ3) (53180310347689/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 8) (s := 4) (r := 1) (v := 2) (t := 7) (D := 8)
    (a := (5/14 : ℝ)) (b := (1/14 : ℝ)) (c := (4/7 : ℝ))
    (by norm_num) half_7_12_φ3 (by norm_num [half_7_12_φ1, half_7_12_φ2, half_7_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_12_φ1, half_7_12_φ2, half_7_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_7_12_hF1 half_7_12_hF2 half_7_11
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_7_12_φ1, half_7_12_φ2, half_7_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_12_hx2 : SourcePowerBound (powerBoxCross 8 5 4 half_7_12_φ2) (30296026074133/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 5) (u := 3) (t := 6)
    (D := 4) (ψ := (263400557967/10000000000000 : ℝ)) half_7_12_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_7_12_φ1, half_7_12_φ2, half_7_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_12_φ1, half_7_12_φ2, half_7_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_7_12_φ1, half_7_12_φ2, half_7_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_4 SeedCompletionEven8SecondSeeds.degree8_half_6
    (by simpa only [half_7_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_7_12_hx3)
  exact h.weaken (by norm_num [half_7_12_φ1, half_7_12_φ2, half_7_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_12_hx1 : SourcePowerBound (powerBoxCross 8 6 2 half_7_12_φ1) (73397573107813/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 6) (u := 4) (t := 7)
    (D := 2) (ψ := (734442186741/10000000000000 : ℝ)) half_7_12_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_7_12_φ1, half_7_12_φ2, half_7_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_12_φ1, half_7_12_φ2, half_7_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_7_12_φ1, half_7_12_φ2, half_7_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_5 half_7_11
    (by simpa only [half_7_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_7_12_hx2)
  exact h.weaken (by norm_num [half_7_12_φ1, half_7_12_φ2, half_7_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_12 : AdmissibleExponent 8 14 (83105994523957/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 5) (ψ := (55161485319/625000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6
    (by simpa only [half_7_12_φ1] using half_7_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_7_12_φ1, half_7_12_φ2, half_7_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_8_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (467768569361/5000000000000 : ℝ)

private def half_8_12_φ2 : Fin 2 → ℝ := Fin.snoc half_8_12_φ1 (206996690573/2500000000000 : ℝ)

private def half_8_12_φ3 : Fin 3 → ℝ := Fin.snoc half_8_12_φ2 (558046535117/10000000000000 : ℝ)

private theorem half_8_12_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_8_12_φ3) (61247020841249/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_12_φ3 (by norm_num [half_8_12_φ1, half_8_12_φ2, half_8_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_12_φ1, half_8_12_φ2, half_8_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_12_φ1, half_8_12_φ2, half_8_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_12_φ1, half_8_12_φ2, half_8_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_12_hx3 : SourcePowerBound (powerBoxCross 8 5 8 half_8_12_φ3) (30190009779689/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 5) (r := 2) (v := 6) (w := 7) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_8_12_φ3 (by norm_num [half_8_12_φ1, half_8_12_φ2, half_8_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_12_φ1, half_8_12_φ2, half_8_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_8_12_hF2 SeedCompletionEven8SecondSeeds.degree8_half_6 half_7_12
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_8_12_φ1, half_8_12_φ2, half_8_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_12_hx2 : SourcePowerBound (powerBoxCross 8 6 4 half_8_12_φ2) (70753912413119/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 6) (u := 4) (t := 7)
    (D := 4) (ψ := (558046535117/10000000000000 : ℝ)) half_8_12_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_12_φ1, half_8_12_φ2, half_8_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_12_φ1, half_8_12_φ2, half_8_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_12_φ1, half_8_12_φ2, half_8_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_5 half_7_12
    (by simpa only [half_8_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_8_12_hx3)
  exact h.weaken (by norm_num [half_8_12_φ1, half_8_12_φ2, half_8_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_12_hx1 : SourcePowerBound (powerBoxCross 8 7 2 half_8_12_φ1) (43133328614961/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 7) (u := 5) (t := 8)
    (D := 2) (ψ := (206996690573/2500000000000 : ℝ)) half_8_12_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_12_φ1, half_8_12_φ2, half_8_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_12_φ1, half_8_12_φ2, half_8_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_12_φ1, half_8_12_φ2, half_8_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6 half_8_11
    (by simpa only [half_8_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_8_12_hx2)
  exact h.weaken (by norm_num [half_8_12_φ1, half_8_12_φ2, half_8_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_12 : AdmissibleExponent 8 16 (24607160008327/2500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 6) (ψ := (467768569361/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_7_12
    (by simpa only [half_8_12_φ1] using half_8_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_8_12_φ1, half_8_12_φ2, half_8_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (123851503887/1250000000000 : ℝ)

private def half_9_12_φ2 : Fin 2 → ℝ := Fin.snoc half_9_12_φ1 (226386033811/2500000000000 : ℝ)

private def half_9_12_φ3 : Fin 3 → ℝ := Fin.snoc half_9_12_φ2 (749321408489/10000000000000 : ℝ)

private theorem half_9_12_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_9_12_φ3) (54440770928591/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_12_φ3 (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_12_hx3 : SourcePowerBound (powerBoxCross 8 6 8 half_9_12_φ3) (67900889332851/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 6) (r := 2) (v := 8) (w := 8) (D := 8)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_9_12_φ3 (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_12_hF2 half_8_12 half_8_12
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_12_hx2 : SourcePowerBound (powerBoxCross 8 7 4 half_9_12_φ2) (40657998961999/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (749321408489/10000000000000 : ℝ)) half_9_12_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6 half_8_12
    (by simpa only [half_9_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_12_hx3)
  exact h.weaken (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_12_hx1 : SourcePowerBound (powerBoxCross 8 8 2 half_9_12_φ1) (9966702398947/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (226386033811/2500000000000 : ℝ)) half_9_12_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_7_12 half_9_11
    (by simpa only [half_9_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_12_hx2)
  exact h.weaken (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_12 : AdmissibleExponent 8 18 (11452920445591/1000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 7) (ψ := (123851503887/1250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_8_12
    (by simpa only [half_9_12_φ1] using half_9_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_7_13_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (882583311717/10000000000000 : ℝ)

private def half_7_13_φ2 : Fin 2 → ℝ := Fin.snoc half_7_13_φ1 (146888396489/2000000000000 : ℝ)

private def half_7_13_φ3 : Fin 3 → ℝ := Fin.snoc half_7_13_φ2 (13169983919/500000000000 : ℝ)

private theorem half_7_13_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_7_13_φ3) (35255537788309/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_13_φ3 (by norm_num [half_7_13_φ1, half_7_13_φ2, half_7_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_13_φ1, half_7_13_φ2, half_7_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_13_φ1, half_7_13_φ2, half_7_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_7_13_φ1, half_7_13_φ2, half_7_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_7_13_hF1 : SourcePowerBound (paddedMoment 8 0 1 8 half_7_13_φ3) (13418512596103/5000000000000 : ℝ) := by
  have h := padded_second_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_13_φ3 (by norm_num [half_7_13_φ1, half_7_13_φ2, half_7_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_13_φ1, half_7_13_φ2, half_7_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_13_φ1, half_7_13_φ2, half_7_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_7_13_φ1, half_7_13_φ2, half_7_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_7_13_hx3 : SourcePowerBound (powerBoxCross 8 4 8 half_7_13_φ3) (53180320553763/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 8) (s := 4) (r := 1) (v := 2) (t := 7) (D := 8)
    (a := (5/14 : ℝ)) (b := (1/14 : ℝ)) (c := (4/7 : ℝ))
    (by norm_num) half_7_13_φ3 (by norm_num [half_7_13_φ1, half_7_13_φ2, half_7_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_13_φ1, half_7_13_φ2, half_7_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_7_13_hF1 half_7_13_hF2 half_7_12
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_7_13_φ1, half_7_13_φ2, half_7_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_13_hx2 : SourcePowerBound (powerBoxCross 8 5 4 half_7_13_φ2) (60592058729393/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 5) (u := 3) (t := 6)
    (D := 4) (ψ := (13169983919/500000000000 : ℝ)) half_7_13_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_7_13_φ1, half_7_13_φ2, half_7_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_13_φ1, half_7_13_φ2, half_7_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_7_13_φ1, half_7_13_φ2, half_7_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_4 SeedCompletionEven8SecondSeeds.degree8_half_6
    (by simpa only [half_7_13_φ3, show (2:ℝ)*4=8 by norm_num] using half_7_13_hx3)
  exact h.weaken (by norm_num [half_7_13_φ1, half_7_13_φ2, half_7_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_13_hx1 : SourcePowerBound (powerBoxCross 8 6 2 half_7_13_φ1) (9174696970393/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 6) (u := 4) (t := 7)
    (D := 2) (ψ := (146888396489/2000000000000 : ℝ)) half_7_13_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_7_13_φ1, half_7_13_φ2, half_7_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_13_φ1, half_7_13_φ2, half_7_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_7_13_φ1, half_7_13_φ2, half_7_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_5 half_7_12
    (by simpa only [half_7_13_φ2, show (2:ℝ)*2=4 by norm_num] using half_7_13_hx2)
  exact h.weaken (by norm_num [half_7_13_φ1, half_7_13_φ2, half_7_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_13 : AdmissibleExponent 8 14 (83105992192031/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 5) (ψ := (882583311717/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6
    (by simpa only [half_7_13_φ1] using half_7_13_hx1)
  exact admissibleExponent_mono h (by norm_num [half_7_13_φ1, half_7_13_φ2, half_7_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_8_13_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (37421411949/400000000000 : ℝ)

private def half_8_13_φ2 : Fin 2 → ℝ := Fin.snoc half_8_13_φ1 (206996623213/2500000000000 : ℝ)

private def half_8_13_φ3 : Fin 3 → ℝ := Fin.snoc half_8_13_φ2 (34877872709/625000000000 : ℝ)

private theorem half_8_13_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_8_13_φ3) (61247077146659/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_13_φ3 (by norm_num [half_8_13_φ1, half_8_13_φ2, half_8_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_13_φ1, half_8_13_φ2, half_8_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_13_φ1, half_8_13_φ2, half_8_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_13_φ1, half_8_13_φ2, half_8_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_13_hx3 : SourcePowerBound (powerBoxCross 8 5 8 half_8_13_φ3) (30190024238859/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 5) (r := 2) (v := 6) (w := 7) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_8_13_φ3 (by norm_num [half_8_13_φ1, half_8_13_φ2, half_8_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_13_φ1, half_8_13_φ2, half_8_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_8_13_hF2 SeedCompletionEven8SecondSeeds.degree8_half_6 half_7_13
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_8_13_φ1, half_8_13_φ2, half_8_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_13_hx2 : SourcePowerBound (powerBoxCross 8 6 4 half_8_13_φ2) (3537696974367/500000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 6) (u := 4) (t := 7)
    (D := 4) (ψ := (34877872709/625000000000 : ℝ)) half_8_13_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_13_φ1, half_8_13_φ2, half_8_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_13_φ1, half_8_13_φ2, half_8_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_13_φ1, half_8_13_φ2, half_8_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_5 half_7_13
    (by simpa only [half_8_13_φ3, show (2:ℝ)*4=8 by norm_num] using half_8_13_hx3)
  exact h.weaken (by norm_num [half_8_13_φ1, half_8_13_φ2, half_8_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_13_hx1 : SourcePowerBound (powerBoxCross 8 7 2 half_8_13_φ1) (2156666714191/250000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 7) (u := 5) (t := 8)
    (D := 2) (ψ := (206996623213/2500000000000 : ℝ)) half_8_13_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_13_φ1, half_8_13_φ2, half_8_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_13_φ1, half_8_13_φ2, half_8_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_13_φ1, half_8_13_φ2, half_8_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6 half_8_12
    (by simpa only [half_8_13_φ2, show (2:ℝ)*2=4 by norm_num] using half_8_13_hx2)
  exact h.weaken (by norm_num [half_8_13_φ1, half_8_13_φ2, half_8_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_13 : AdmissibleExponent 8 16 (19685725490213/2000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 6) (ψ := (37421411949/400000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_7_13
    (by simpa only [half_8_13_φ1] using half_8_13_hx1)
  exact admissibleExponent_mono h (by norm_num [half_8_13_φ1, half_8_13_φ2, half_8_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_13_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (495401857869/5000000000000 : ℝ)

private def half_9_13_φ2 : Fin 2 → ℝ := Fin.snoc half_9_13_φ1 (905542896649/10000000000000 : ℝ)

private def half_9_13_φ3 : Fin 3 → ℝ := Fin.snoc half_9_13_φ2 (46832416097/625000000000 : ℝ)

private theorem half_9_13_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_9_13_φ3) (54441029331281/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_13_φ3 (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_13_hx3 : SourcePowerBound (powerBoxCross 8 6 8 half_9_13_φ3) (67901037829991/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 6) (r := 2) (v := 8) (w := 8) (D := 8)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_9_13_φ3 (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_13_hF2 half_8_13 half_8_13
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_13_hx2 : SourcePowerBound (powerBoxCross 8 7 4 half_9_13_φ2) (40658066201137/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (46832416097/625000000000 : ℝ)) half_9_13_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6 half_8_13
    (by simpa only [half_9_13_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_13_hx3)
  exact h.weaken (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_13_hx1 : SourcePowerBound (powerBoxCross 8 8 2 half_9_13_φ1) (6229192886591/625000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (905542896649/10000000000000 : ℝ)) half_9_13_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_7_13 half_9_12
    (by simpa only [half_9_13_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_13_hx2)
  exact h.weaken (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_13 : AdmissibleExponent 8 18 (57264570960763/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 7) (ψ := (495401857869/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_8_13
    (by simpa only [half_9_13_φ1] using half_9_13_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_13_φ1, half_9_13_φ2, half_9_13_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_7_14_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (110322895059/1250000000000 : ℝ)

private def half_7_14_φ2 : Fin 2 → ℝ := Fin.snoc half_7_14_φ1 (367220957147/5000000000000 : ℝ)

private def half_7_14_φ3 : Fin 3 → ℝ := Fin.snoc half_7_14_φ2 (131699692479/5000000000000 : ℝ)

private theorem half_7_14_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_7_14_φ3) (17627771586449/2500000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_14_φ3 (by norm_num [half_7_14_φ1, half_7_14_φ2, half_7_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_14_φ1, half_7_14_φ2, half_7_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_14_φ1, half_7_14_φ2, half_7_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_7_14_φ1, half_7_14_φ2, half_7_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_7_14_hF1 : SourcePowerBound (paddedMoment 8 0 1 8 half_7_14_φ3) (6709257195483/2500000000000 : ℝ) := by
  have h := padded_second_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_14_φ3 (by norm_num [half_7_14_φ1, half_7_14_φ2, half_7_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_14_φ1, half_7_14_φ2, half_7_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_14_φ1, half_7_14_φ2, half_7_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_7_14_φ1, half_7_14_φ2, half_7_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_7_14_hx3 : SourcePowerBound (powerBoxCross 8 4 8 half_7_14_φ3) (26590161979203/5000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 8) (s := 4) (r := 1) (v := 2) (t := 7) (D := 8)
    (a := (5/14 : ℝ)) (b := (1/14 : ℝ)) (c := (4/7 : ℝ))
    (by norm_num) half_7_14_φ3 (by norm_num [half_7_14_φ1, half_7_14_φ2, half_7_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_14_φ1, half_7_14_φ2, half_7_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_7_14_hF1 half_7_14_hF2 half_7_13
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_7_14_φ1, half_7_14_φ2, half_7_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_14_hx2 : SourcePowerBound (powerBoxCross 8 5 4 half_7_14_φ2) (3787003807799/625000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 5) (u := 3) (t := 6)
    (D := 4) (ψ := (131699692479/5000000000000 : ℝ)) half_7_14_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_7_14_φ1, half_7_14_φ2, half_7_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_14_φ1, half_7_14_φ2, half_7_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_7_14_φ1, half_7_14_φ2, half_7_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_4 SeedCompletionEven8SecondSeeds.degree8_half_6
    (by simpa only [half_7_14_φ3, show (2:ℝ)*4=8 by norm_num] using half_7_14_hx3)
  exact h.weaken (by norm_num [half_7_14_φ1, half_7_14_φ2, half_7_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_14_hx1 : SourcePowerBound (powerBoxCross 8 6 2 half_7_14_φ1) (73397576648929/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 6) (u := 4) (t := 7)
    (D := 2) (ψ := (367220957147/5000000000000 : ℝ)) half_7_14_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_7_14_φ1, half_7_14_φ2, half_7_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_14_φ1, half_7_14_φ2, half_7_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_7_14_φ1, half_7_14_φ2, half_7_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_5 half_7_13
    (by simpa only [half_7_14_φ2, show (2:ℝ)*2=4 by norm_num] using half_7_14_hx2)
  exact h.weaken (by norm_num [half_7_14_φ1, half_7_14_φ2, half_7_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_14 : AdmissibleExponent 8 14 (83105991414121/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 5) (ψ := (110322895059/1250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6
    (by simpa only [half_7_14_φ1] using half_7_14_hx1)
  exact admissibleExponent_mono h (by norm_num [half_7_14_φ1, half_7_14_φ2, half_7_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_8_14_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (116941830959/1250000000000 : ℝ)

private def half_8_14_φ2 : Fin 2 → ℝ := Fin.snoc half_8_14_φ1 (413993200447/5000000000000 : ℝ)

private def half_8_14_φ3 : Fin 3 → ℝ := Fin.snoc half_8_14_φ2 (111609152893/2000000000000 : ℝ)

private theorem half_8_14_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_8_14_φ3) (61247096926349/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_14_φ3 (by norm_num [half_8_14_φ1, half_8_14_φ2, half_8_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_14_φ1, half_8_14_φ2, half_8_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_14_φ1, half_8_14_φ2, half_8_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_14_φ1, half_8_14_φ2, half_8_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_14_hx3 : SourcePowerBound (powerBoxCross 8 5 8 half_8_14_φ3) (60380058652373/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 5) (r := 2) (v := 6) (w := 7) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_8_14_φ3 (by norm_num [half_8_14_φ1, half_8_14_φ2, half_8_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_14_φ1, half_8_14_φ2, half_8_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_8_14_hF2 SeedCompletionEven8SecondSeeds.degree8_half_6 half_7_14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_8_14_φ1, half_8_14_φ2, half_8_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_14_hx2 : SourcePowerBound (powerBoxCross 8 6 4 half_8_14_φ2) (35376974523661/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 6) (u := 4) (t := 7)
    (D := 4) (ψ := (111609152893/2000000000000 : ℝ)) half_8_14_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_14_φ1, half_8_14_φ2, half_8_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_14_φ1, half_8_14_φ2, half_8_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_14_φ1, half_8_14_φ2, half_8_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_5 half_7_14
    (by simpa only [half_8_14_φ3, show (2:ℝ)*4=8 by norm_num] using half_8_14_hx3)
  exact h.weaken (by norm_num [half_8_14_φ1, half_8_14_φ2, half_8_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_14_hx1 : SourcePowerBound (powerBoxCross 8 7 2 half_8_14_φ1) (17253334524419/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 7) (u := 5) (t := 8)
    (D := 2) (ψ := (413993200447/5000000000000 : ℝ)) half_8_14_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_14_φ1, half_8_14_φ2, half_8_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_14_φ1, half_8_14_φ2, half_8_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_14_φ1, half_8_14_φ2, half_8_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6 half_8_13
    (by simpa only [half_8_14_φ2, show (2:ℝ)*2=4 by norm_num] using half_8_14_hx2)
  exact h.weaken (by norm_num [half_8_14_φ1, half_8_14_φ2, half_8_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_14 : AdmissibleExponent 8 16 (98428623041831/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 6) (ψ := (116941830959/1250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_7_14
    (by simpa only [half_8_14_φ1] using half_8_14_hx1)
  exact admissibleExponent_mono h (by norm_num [half_8_14_φ1, half_8_14_φ2, half_8_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_14_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (198160101117/2000000000000 : ℝ)

private def half_9_14_φ2 : Fin 2 → ℝ := Fin.snoc half_9_14_φ1 (905542441759/10000000000000 : ℝ)

private def half_9_14_φ3 : Fin 3 → ℝ := Fin.snoc half_9_14_φ2 (374658818119/5000000000000 : ℝ)

private theorem half_9_14_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_9_14_φ3) (27220563872389/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_14_φ3 (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_14_hx3 : SourcePowerBound (powerBoxCross 8 6 8 half_9_14_φ3) (67901094596717/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 6) (r := 2) (v := 8) (w := 8) (D := 8)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_9_14_φ3 (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_14_hF2 half_8_14 half_8_14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_14_hx2 : SourcePowerBound (powerBoxCross 8 7 4 half_9_14_φ2) (20329046061693/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (374658818119/5000000000000 : ℝ)) half_9_14_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6 half_8_14
    (by simpa only [half_9_14_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_14_hx3)
  exact h.weaken (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_14_hx1 : SourcePowerBound (powerBoxCross 8 8 2 half_9_14_φ1) (3114597206251/312500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (905542441759/10000000000000 : ℝ)) half_9_14_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_7_14 half_9_13
    (by simpa only [half_9_14_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_14_hx2)
  exact h.weaken (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_14 : AdmissibleExponent 8 18 (114529118183807/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 7) (ψ := (198160101117/2000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_8_14
    (by simpa only [half_9_14_φ1] using half_9_14_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_14_φ1, half_9_14_φ2, half_9_14_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_7_15_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (882583110017/10000000000000 : ℝ)

private def half_7_15_φ2 : Fin 2 → ℝ := Fin.snoc half_7_15_φ1 (734441891559/10000000000000 : ℝ)

private def half_7_15_φ3 : Fin 3 → ℝ := Fin.snoc half_7_15_φ2 (10535971483/400000000000 : ℝ)

private theorem half_7_15_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_7_15_φ3) (70511089938329/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_15_φ3 (by norm_num [half_7_15_φ1, half_7_15_φ2, half_7_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_15_φ1, half_7_15_φ2, half_7_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_15_φ1, half_7_15_φ2, half_7_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_7_15_φ1, half_7_15_φ2, half_7_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_7_15_hF1 : SourcePowerBound (paddedMoment 8 0 1 8 half_7_15_φ3) (26837029979443/10000000000000 : ℝ) := by
  have h := padded_second_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_15_φ3 (by norm_num [half_7_15_φ1, half_7_15_φ2, half_7_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_15_φ1, half_7_15_φ2, half_7_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_15_φ1, half_7_15_φ2, half_7_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_7_15_φ1, half_7_15_φ2, half_7_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_7_15_hx3 : SourcePowerBound (powerBoxCross 8 4 8 half_7_15_φ3) (26590162547089/5000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 8) (s := 4) (r := 1) (v := 2) (t := 7) (D := 8)
    (a := (5/14 : ℝ)) (b := (1/14 : ℝ)) (c := (4/7 : ℝ))
    (by norm_num) half_7_15_φ3 (by norm_num [half_7_15_φ1, half_7_15_φ2, half_7_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_15_φ1, half_7_15_φ2, half_7_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_7_15_hF1 half_7_15_hF2 half_7_14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_7_15_φ1, half_7_15_φ2, half_7_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_15_hx2 : SourcePowerBound (powerBoxCross 8 5 4 half_7_15_φ2) (30296030828583/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 5) (u := 3) (t := 6)
    (D := 4) (ψ := (10535971483/400000000000 : ℝ)) half_7_15_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_7_15_φ1, half_7_15_φ2, half_7_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_15_φ1, half_7_15_φ2, half_7_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_7_15_φ1, half_7_15_φ2, half_7_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_4 SeedCompletionEven8SecondSeeds.degree8_half_6
    (by simpa only [half_7_15_φ3, show (2:ℝ)*4=8 by norm_num] using half_7_15_hx3)
  exact h.weaken (by norm_num [half_7_15_φ1, half_7_15_φ2, half_7_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_15_hx1 : SourcePowerBound (powerBoxCross 8 6 2 half_7_15_φ1) (36698788472217/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 6) (u := 4) (t := 7)
    (D := 2) (ψ := (734441891559/10000000000000 : ℝ)) half_7_15_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_7_15_φ1, half_7_15_φ2, half_7_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_15_φ1, half_7_15_φ2, half_7_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_7_15_φ1, half_7_15_φ2, half_7_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_5 half_7_14
    (by simpa only [half_7_15_φ2, show (2:ℝ)*2=4 by norm_num] using half_7_15_hx2)
  exact h.weaken (by norm_num [half_7_15_φ1, half_7_15_φ2, half_7_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_15 : AdmissibleExponent 8 14 (83105991154621/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 5) (ψ := (882583110017/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6
    (by simpa only [half_7_15_φ1] using half_7_15_hx1)
  exact admissibleExponent_mono h (by norm_num [half_7_15_φ1, half_7_15_φ2, half_7_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_8_15_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (935534418323/10000000000000 : ℝ)

private def half_8_15_φ2 : Fin 2 → ℝ := Fin.snoc half_8_15_φ1 (41399318477/500000000000 : ℝ)

private def half_8_15_φ3 : Fin 3 → ℝ := Fin.snoc half_8_15_φ2 (279022847731/5000000000000 : ℝ)

private theorem half_8_15_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_8_15_φ3) (2449884154007/400000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_15_φ3 (by norm_num [half_8_15_φ1, half_8_15_φ2, half_8_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_15_φ1, half_8_15_φ2, half_8_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_15_φ1, half_8_15_φ2, half_8_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_15_φ1, half_8_15_φ2, half_8_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_15_hx3 : SourcePowerBound (powerBoxCross 8 5 8 half_8_15_φ3) (603800622189/100000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 5) (r := 2) (v := 6) (w := 7) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_8_15_φ3 (by norm_num [half_8_15_φ1, half_8_15_φ2, half_8_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_15_φ1, half_8_15_φ2, half_8_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_8_15_hF2 SeedCompletionEven8SecondSeeds.degree8_half_6 half_7_15
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_8_15_φ1, half_8_15_φ2, half_8_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_15_hx2 : SourcePowerBound (powerBoxCross 8 6 4 half_8_15_φ2) (70753952408963/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 6) (u := 4) (t := 7)
    (D := 4) (ψ := (279022847731/5000000000000 : ℝ)) half_8_15_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_15_φ1, half_8_15_φ2, half_8_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_15_φ1, half_8_15_φ2, half_8_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_15_φ1, half_8_15_φ2, half_8_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_5 half_7_15
    (by simpa only [half_8_15_φ3, show (2:ℝ)*4=8 by norm_num] using half_8_15_hx3)
  exact h.weaken (by norm_num [half_8_15_φ1, half_8_15_φ2, half_8_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_15_hx1 : SourcePowerBound (powerBoxCross 8 7 2 half_8_15_φ1) (21566668515887/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 7) (u := 5) (t := 8)
    (D := 2) (ψ := (41399318477/500000000000 : ℝ)) half_8_15_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_15_φ1, half_8_15_φ2, half_8_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_15_φ1, half_8_15_φ2, half_8_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_15_φ1, half_8_15_φ2, half_8_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6 half_8_14
    (by simpa only [half_8_15_φ2, show (2:ℝ)*2=4 by norm_num] using half_8_15_hx2)
  exact h.weaken (by norm_num [half_8_15_φ1, half_8_15_φ2, half_8_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_15 : AdmissibleExponent 8 16 (98428621501747/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 6) (ψ := (935534418323/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_7_15
    (by simpa only [half_8_15_φ1] using half_8_15_hx1)
  exact admissibleExponent_mono h (by norm_num [half_8_15_φ1, half_8_15_φ2, half_8_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_15_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (990799276119/10000000000000 : ℝ)

private def half_9_15_φ2 : Fin 2 → ℝ := Fin.snoc half_9_15_φ1 (452771137743/5000000000000 : ℝ)

private def half_9_15_φ3 : Fin 3 → ℝ := Fin.snoc half_9_15_φ2 (749317258617/10000000000000 : ℝ)

private theorem half_9_15_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_9_15_φ3) (27220582492669/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_15_φ3 (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_15_hx3 : SourcePowerBound (powerBoxCross 8 6 8 half_9_15_φ3) (67901116148587/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 6) (r := 2) (v := 8) (w := 8) (D := 8)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_9_15_φ3 (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_15_hF2 half_8_15 half_8_15
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_15_hx2 : SourcePowerBound (powerBoxCross 8 7 4 half_9_15_φ2) (16263240815179/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (749317258617/10000000000000 : ℝ)) half_9_15_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6 half_8_15
    (by simpa only [half_9_15_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_15_hx3)
  exact h.weaken (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_15_hx1 : SourcePowerBound (powerBoxCross 8 8 2 half_9_15_φ1) (99667120084541/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (452771137743/5000000000000 : ℝ)) half_9_15_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_7_15 half_9_14
    (by simpa only [half_9_15_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_15_hx2)
  exact h.weaken (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_15 : AdmissibleExponent 8 18 (57264554613163/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 7) (ψ := (990799276119/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_8_15
    (by simpa only [half_9_15_φ1] using half_9_15_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_7_16_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (882583093187/10000000000000 : ℝ)

private def half_7_16_φ2 : Fin 2 → ℝ := Fin.snoc half_7_16_φ1 (29377675359/400000000000 : ℝ)

private def half_7_16_φ3 : Fin 3 → ℝ := Fin.snoc half_7_16_φ2 (131699627211/5000000000000 : ℝ)

private theorem half_7_16_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_7_16_φ3) (2203471598023/312500000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_16_φ3 (by norm_num [half_7_16_φ1, half_7_16_φ2, half_7_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_16_φ1, half_7_16_φ2, half_7_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_16_φ1, half_7_16_φ2, half_7_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_7_16_φ1, half_7_16_φ2, half_7_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_7_16_hF1 : SourcePowerBound (paddedMoment 8 0 1 8 half_7_16_φ3) (838657199341/312500000000 : ℝ) := by
  have h := padded_second_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_16_φ3 (by norm_num [half_7_16_φ1, half_7_16_φ2, half_7_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_16_φ1, half_7_16_φ2, half_7_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_16_φ1, half_7_16_φ2, half_7_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_7_16_φ1, half_7_16_φ2, half_7_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_7_16_hx3 : SourcePowerBound (powerBoxCross 8 4 8 half_7_16_φ3) (53180325473051/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 8) (s := 4) (r := 1) (v := 2) (t := 7) (D := 8)
    (a := (5/14 : ℝ)) (b := (1/14 : ℝ)) (c := (4/7 : ℝ))
    (by norm_num) half_7_16_φ3 (by norm_num [half_7_16_φ1, half_7_16_φ2, half_7_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_16_φ1, half_7_16_φ2, half_7_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_7_16_hF1 half_7_16_hF2 half_7_15
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_7_16_φ1, half_7_16_φ2, half_7_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_16_hx2 : SourcePowerBound (powerBoxCross 8 5 4 half_7_16_φ2) (60592061901463/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 5) (u := 3) (t := 6)
    (D := 4) (ψ := (131699627211/5000000000000 : ℝ)) half_7_16_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_7_16_φ1, half_7_16_φ2, half_7_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_16_φ1, half_7_16_φ2, half_7_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_7_16_φ1, half_7_16_φ2, half_7_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_4 SeedCompletionEven8SecondSeeds.degree8_half_6
    (by simpa only [half_7_16_φ3, show (2:ℝ)*4=8 by norm_num] using half_7_16_hx3)
  exact h.weaken (by norm_num [half_7_16_φ1, half_7_16_φ2, half_7_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_16_hx1 : SourcePowerBound (powerBoxCross 8 6 2 half_7_16_φ1) (14679515408599/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 6) (u := 4) (t := 7)
    (D := 2) (ψ := (29377675359/400000000000 : ℝ)) half_7_16_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_7_16_φ1, half_7_16_φ2, half_7_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_16_φ1, half_7_16_φ2, half_7_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_7_16_φ1, half_7_16_φ2, half_7_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_5 half_7_15
    (by simpa only [half_7_16_φ2, show (2:ℝ)*2=4 by norm_num] using half_7_16_hx2)
  exact h.weaken (by norm_num [half_7_16_φ1, half_7_16_φ2, half_7_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_16 : AdmissibleExponent 8 14 (20776497767013/2500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 5) (ψ := (882583093187/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6
    (by simpa only [half_7_16_φ1] using half_7_16_hx1)
  exact admissibleExponent_mono h (by norm_num [half_7_16_φ1, half_7_16_φ2, half_7_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_8_16_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (467767168921/5000000000000 : ℝ)

private def half_8_16_φ2 : Fin 2 → ℝ := Fin.snoc half_8_16_φ1 (827986358859/10000000000000 : ℝ)

private def half_8_16_φ3 : Fin 3 → ℝ := Fin.snoc half_8_16_φ2 (69755708947/1250000000000 : ℝ)

private theorem half_8_16_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_8_16_φ3) (61247106266183/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_16_φ3 (by norm_num [half_8_16_φ1, half_8_16_φ2, half_8_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_16_φ1, half_8_16_φ2, half_8_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_16_φ1, half_8_16_φ2, half_8_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_16_φ1, half_8_16_φ2, half_8_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_16_hx3 : SourcePowerBound (powerBoxCross 8 5 8 half_8_16_φ3) (7547507933117/1250000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 5) (r := 2) (v := 6) (w := 7) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_8_16_φ3 (by norm_num [half_8_16_φ1, half_8_16_φ2, half_8_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_16_φ1, half_8_16_φ2, half_8_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_8_16_hF2 SeedCompletionEven8SecondSeeds.degree8_half_6 half_7_16
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_8_16_φ1, half_8_16_φ2, half_8_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_16_hx2 : SourcePowerBound (powerBoxCross 8 6 4 half_8_16_φ2) (14150790717343/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 6) (u := 4) (t := 7)
    (D := 4) (ψ := (69755708947/1250000000000 : ℝ)) half_8_16_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_16_φ1, half_8_16_φ2, half_8_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_16_φ1, half_8_16_φ2, half_8_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_16_φ1, half_8_16_φ2, half_8_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_5 half_7_16
    (by simpa only [half_8_16_φ3, show (2:ℝ)*4=8 by norm_num] using half_8_16_hx3)
  exact h.weaken (by norm_num [half_8_16_φ1, half_8_16_φ2, half_8_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_16_hx1 : SourcePowerBound (powerBoxCross 8 7 2 half_8_16_φ1) (43133337286721/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 7) (u := 5) (t := 8)
    (D := 2) (ψ := (827986358859/10000000000000 : ℝ)) half_8_16_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_16_φ1, half_8_16_φ2, half_8_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_16_φ1, half_8_16_φ2, half_8_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_16_φ1, half_8_16_φ2, half_8_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6 half_8_15
    (by simpa only [half_8_16_φ2, show (2:ℝ)*2=4 by norm_num] using half_8_16_hx2)
  exact h.weaken (by norm_num [half_8_16_φ1, half_8_16_φ2, half_8_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_16 : AdmissibleExponent 8 16 (24607155241347/2500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 6) (ψ := (467767168921/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_7_16
    (by simpa only [half_8_16_φ1] using half_8_16_hx1)
  exact admissibleExponent_mono h (by norm_num [half_8_16_φ1, half_8_16_φ2, half_8_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_16_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (990798808513/10000000000000 : ℝ)

private def half_9_16_φ2 : Fin 2 → ℝ := Fin.snoc half_9_16_φ1 (226385553739/2500000000000 : ℝ)

private def half_9_16_φ3 : Fin 3 → ℝ := Fin.snoc half_9_16_φ2 (149863423901/2000000000000 : ℝ)

private theorem half_9_16_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_9_16_φ3) (27220589498773/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_16_φ3 (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_16_hx3 : SourcePowerBound (powerBoxCross 8 6 8 half_9_16_φ3) (67901124281519/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 6) (r := 2) (v := 8) (w := 8) (D := 8)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_9_16_φ3 (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_16_hF2 half_8_16 half_8_16
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_16_hx2 : SourcePowerBound (powerBoxCross 8 7 4 half_9_16_φ2) (81316211607583/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (149863423901/2000000000000 : ℝ)) half_9_16_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6 half_8_16
    (by simpa only [half_9_16_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_16_hx3)
  exact h.weaken (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_16_hx1 : SourcePowerBound (powerBoxCross 8 8 2 half_9_16_φ1) (99667123736299/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (226385553739/2500000000000 : ℝ)) half_9_16_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_7_16 half_9_15
    (by simpa only [half_9_16_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_16_hx2)
  exact h.weaken (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_16 : AdmissibleExponent 8 18 (57264552931997/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 7) (ψ := (990798808513/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_8_16
    (by simpa only [half_9_16_φ1] using half_9_16_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_16_φ1, half_9_16_φ2, half_9_16_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_7_17_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (220645771893/2500000000000 : ℝ)

private def half_7_17_φ2 : Fin 2 → ℝ := Fin.snoc half_7_17_φ1 (146888376289/2000000000000 : ℝ)

private def half_7_17_φ3 : Fin 3 → ℝ := Fin.snoc half_7_17_φ2 (263399243529/10000000000000 : ℝ)

private theorem half_7_17_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_7_17_φ3) (35255545768267/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_17_φ3 (by norm_num [half_7_17_φ1, half_7_17_φ2, half_7_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_17_φ1, half_7_17_φ2, half_7_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_17_φ1, half_7_17_φ2, half_7_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_7_17_φ1, half_7_17_φ2, half_7_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_7_17_hF1 : SourcePowerBound (paddedMoment 8 0 1 8 half_7_17_φ3) (13418515256089/5000000000000 : ℝ) := by
  have h := padded_second_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_17_φ3 (by norm_num [half_7_17_φ1, half_7_17_φ2, half_7_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_17_φ1, half_7_17_φ2, half_7_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_17_φ1, half_7_17_φ2, half_7_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_7_17_φ1, half_7_17_φ2, half_7_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_7_17_hx3 : SourcePowerBound (powerBoxCross 8 4 8 half_7_17_φ3) (26590162799723/5000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 8) (s := 4) (r := 1) (v := 2) (t := 7) (D := 8)
    (a := (5/14 : ℝ)) (b := (1/14 : ℝ)) (c := (4/7 : ℝ))
    (by norm_num) half_7_17_φ3 (by norm_num [half_7_17_φ1, half_7_17_φ2, half_7_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_17_φ1, half_7_17_φ2, half_7_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_7_17_hF1 half_7_17_hF2 half_7_16
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_7_17_φ1, half_7_17_φ2, half_7_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_17_hx2 : SourcePowerBound (powerBoxCross 8 5 4 half_7_17_φ2) (60592061982967/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 5) (u := 3) (t := 6)
    (D := 4) (ψ := (263399243529/10000000000000 : ℝ)) half_7_17_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_7_17_φ1, half_7_17_φ2, half_7_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_17_φ1, half_7_17_φ2, half_7_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_7_17_φ1, half_7_17_φ2, half_7_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_4 SeedCompletionEven8SecondSeeds.degree8_half_6
    (by simpa only [half_7_17_φ3, show (2:ℝ)*4=8 by norm_num] using half_7_17_hx3)
  exact h.weaken (by norm_num [half_7_17_φ1, half_7_17_φ2, half_7_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_17_hx1 : SourcePowerBound (powerBoxCross 8 6 2 half_7_17_φ1) (36698788537941/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 6) (u := 4) (t := 7)
    (D := 2) (ψ := (146888376289/2000000000000 : ℝ)) half_7_17_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_7_17_φ1, half_7_17_φ2, half_7_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_17_φ1, half_7_17_φ2, half_7_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_7_17_φ1, half_7_17_φ2, half_7_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_5 half_7_16
    (by simpa only [half_7_17_φ2, show (2:ℝ)*2=4 by norm_num] using half_7_17_hx2)
  exact h.weaken (by norm_num [half_7_17_φ1, half_7_17_φ2, half_7_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_17 : AdmissibleExponent 8 14 (41552995519587/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 5) (ψ := (220645771893/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6
    (by simpa only [half_7_17_φ1] using half_7_17_hx1)
  exact admissibleExponent_mono h (by norm_num [half_7_17_φ1, half_7_17_φ2, half_7_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_8_17_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (935534309697/10000000000000 : ℝ)

private def half_8_17_φ2 : Fin 2 → ℝ := Fin.snoc half_8_17_φ1 (103498294403/1250000000000 : ℝ)

private def half_8_17_φ3 : Fin 3 → ℝ := Fin.snoc half_8_17_φ2 (139511415831/2500000000000 : ℝ)

private theorem half_8_17_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_8_17_φ3) (12249421421371/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_17_φ3 (by norm_num [half_8_17_φ1, half_8_17_φ2, half_8_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_17_φ1, half_8_17_φ2, half_8_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_17_φ1, half_8_17_φ2, half_8_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_17_φ1, half_8_17_φ2, half_8_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_17_hx3 : SourcePowerBound (powerBoxCross 8 5 8 half_8_17_φ3) (60380063898983/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 5) (r := 2) (v := 6) (w := 7) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_8_17_φ3 (by norm_num [half_8_17_φ1, half_8_17_φ2, half_8_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_17_φ1, half_8_17_φ2, half_8_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_8_17_hF2 SeedCompletionEven8SecondSeeds.degree8_half_6 half_7_17
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_8_17_φ1, half_8_17_φ2, half_8_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_17_hx2 : SourcePowerBound (powerBoxCross 8 6 4 half_8_17_φ2) (70753953997997/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 6) (u := 4) (t := 7)
    (D := 4) (ψ := (139511415831/2500000000000 : ℝ)) half_8_17_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_17_φ1, half_8_17_φ2, half_8_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_17_φ1, half_8_17_φ2, half_8_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_17_φ1, half_8_17_φ2, half_8_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_5 half_7_17
    (by simpa only [half_8_17_φ3, show (2:ℝ)*4=8 by norm_num] using half_8_17_hx3)
  exact h.weaken (by norm_num [half_8_17_φ1, half_8_17_φ2, half_8_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_17_hx1 : SourcePowerBound (powerBoxCross 8 7 2 half_8_17_φ1) (86266674753021/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 7) (u := 5) (t := 8)
    (D := 2) (ψ := (103498294403/1250000000000 : ℝ)) half_8_17_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_17_φ1, half_8_17_φ2, half_8_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_17_φ1, half_8_17_φ2, half_8_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_17_φ1, half_8_17_φ2, half_8_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6 half_8_16
    (by simpa only [half_8_17_φ2, show (2:ℝ)*2=4 by norm_num] using half_8_17_hx2)
  exact h.weaken (by norm_num [half_8_17_φ1, half_8_17_φ2, half_8_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_17 : AdmissibleExponent 8 16 (49214310389541/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 6) (ψ := (935534309697/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_7_17
    (by simpa only [half_8_17_φ1] using half_8_17_hx1)
  exact admissibleExponent_mono h (by norm_num [half_8_17_φ1, half_8_17_φ2, half_8_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_17_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (495399315879/5000000000000 : ℝ)

private def half_9_17_φ2 : Fin 2 → ℝ := Fin.snoc half_9_17_φ1 (452771096499/5000000000000 : ℝ)

private def half_9_17_φ3 : Fin 3 → ℝ := Fin.snoc half_9_17_φ2 (374658534213/5000000000000 : ℝ)

private theorem half_9_17_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_9_17_φ3) (27220592121589/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_17_φ3 (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_17_hx3 : SourcePowerBound (powerBoxCross 8 6 8 half_9_17_φ3) (67901127334167/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 6) (r := 2) (v := 8) (w := 8) (D := 8)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_9_17_φ3 (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_17_hF2 half_8_17 half_8_17
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_17_hx2 : SourcePowerBound (powerBoxCross 8 7 4 half_9_17_φ2) (20329053612733/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (374658534213/5000000000000 : ℝ)) half_9_17_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6 half_8_17
    (by simpa only [half_9_17_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_17_hx3)
  exact h.weaken (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_17_hx1 : SourcePowerBound (powerBoxCross 8 8 2 half_9_17_φ1) (6229195320717/625000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (452771096499/5000000000000 : ℝ)) half_9_17_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_7_17 half_9_16
    (by simpa only [half_9_17_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_17_hx2)
  exact h.weaken (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_17 : AdmissibleExponent 8 18 (57264552303921/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 7) (ψ := (495399315879/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_8_17
    (by simpa only [half_9_17_φ1] using half_9_17_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_7_18_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (882583085699/10000000000000 : ℝ)

private def half_7_18_φ2 : Fin 2 → ℝ := Fin.snoc half_7_18_φ1 (734441880601/10000000000000 : ℝ)

private def half_7_18_φ3 : Fin 3 → ℝ := Fin.snoc half_7_18_φ2 (32924904987/1250000000000 : ℝ)

private theorem half_7_18_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_7_18_φ3) (17627772917471/2500000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_18_φ3 (by norm_num [half_7_18_φ1, half_7_18_φ2, half_7_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_18_φ1, half_7_18_φ2, half_7_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_18_φ1, half_7_18_φ2, half_7_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_7_18_φ1, half_7_18_φ2, half_7_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_7_18_hF1 : SourcePowerBound (paddedMoment 8 0 1 8 half_7_18_φ3) (6709257639157/2500000000000 : ℝ) := by
  have h := padded_second_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_18_φ3 (by norm_num [half_7_18_φ1, half_7_18_φ2, half_7_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_18_φ1, half_7_18_φ2, half_7_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_18_φ1, half_7_18_φ2, half_7_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_7_18_φ1, half_7_18_φ2, half_7_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_7_18_hx3 : SourcePowerBound (powerBoxCross 8 4 8 half_7_18_φ3) (53180325641603/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 8) (s := 4) (r := 1) (v := 2) (t := 7) (D := 8)
    (a := (5/14 : ℝ)) (b := (1/14 : ℝ)) (c := (4/7 : ℝ))
    (by norm_num) half_7_18_φ3 (by norm_num [half_7_18_φ1, half_7_18_φ2, half_7_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_18_φ1, half_7_18_φ2, half_7_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_7_18_hF1 half_7_18_hF2 half_7_17
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_7_18_φ1, half_7_18_φ2, half_7_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_18_hx2 : SourcePowerBound (powerBoxCross 8 5 4 half_7_18_φ2) (12118412402031/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 5) (u := 3) (t := 6)
    (D := 4) (ψ := (32924904987/1250000000000 : ℝ)) half_7_18_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_7_18_φ1, half_7_18_φ2, half_7_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_18_φ1, half_7_18_φ2, half_7_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_7_18_φ1, half_7_18_φ2, half_7_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_4 SeedCompletionEven8SecondSeeds.degree8_half_6
    (by simpa only [half_7_18_φ3, show (2:ℝ)*4=8 by norm_num] using half_7_18_hx3)
  exact h.weaken (by norm_num [half_7_18_φ1, half_7_18_φ2, half_7_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_18_hx1 : SourcePowerBound (powerBoxCross 8 6 2 half_7_18_φ1) (18349394271713/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 6) (u := 4) (t := 7)
    (D := 2) (ψ := (734441880601/10000000000000 : ℝ)) half_7_18_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_7_18_φ1, half_7_18_φ2, half_7_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_18_φ1, half_7_18_φ2, half_7_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_7_18_φ1, half_7_18_φ2, half_7_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_5 half_7_17
    (by simpa only [half_7_18_φ2, show (2:ℝ)*2=4 by norm_num] using half_7_18_hx2)
  exact h.weaken (by norm_num [half_7_18_φ1, half_7_18_φ2, half_7_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_18 : AdmissibleExponent 8 14 (83105991029541/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 5) (ψ := (882583085699/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6
    (by simpa only [half_7_18_φ1] using half_7_18_hx1)
  exact admissibleExponent_mono h (by norm_num [half_7_18_φ1, half_7_18_φ2, half_7_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_8_18_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (233883574971/2500000000000 : ℝ)

private def half_8_18_φ2 : Fin 2 → ℝ := Fin.snoc half_8_18_φ1 (827986353987/10000000000000 : ℝ)

private def half_8_18_φ3 : Fin 3 → ℝ := Fin.snoc half_8_18_φ2 (279022830239/5000000000000 : ℝ)

private theorem half_8_18_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_8_18_φ3) (61247107398671/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_18_φ3 (by norm_num [half_8_18_φ1, half_8_18_φ2, half_8_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_18_φ1, half_8_18_φ2, half_8_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_18_φ1, half_8_18_φ2, half_8_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_18_φ1, half_8_18_φ2, half_8_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_18_hx3 : SourcePowerBound (powerBoxCross 8 5 8 half_8_18_φ3) (60380064049801/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 5) (r := 2) (v := 6) (w := 7) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_8_18_φ3 (by norm_num [half_8_18_φ1, half_8_18_φ2, half_8_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_18_φ1, half_8_18_φ2, half_8_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_8_18_hF2 SeedCompletionEven8SecondSeeds.degree8_half_6 half_7_18
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_8_18_φ1, half_8_18_φ2, half_8_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_18_hx2 : SourcePowerBound (powerBoxCross 8 6 4 half_8_18_φ2) (70753954141223/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 6) (u := 4) (t := 7)
    (D := 4) (ψ := (279022830239/5000000000000 : ℝ)) half_8_18_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_18_φ1, half_8_18_φ2, half_8_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_18_φ1, half_8_18_φ2, half_8_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_18_φ1, half_8_18_φ2, half_8_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_5 half_7_18
    (by simpa only [half_8_18_φ3, show (2:ℝ)*4=8 by norm_num] using half_8_18_hx3)
  exact h.weaken (by norm_num [half_8_18_φ1, half_8_18_φ2, half_8_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_18_hx1 : SourcePowerBound (powerBoxCross 8 7 2 half_8_18_φ1) (2695833588001/312500000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 7) (u := 5) (t := 8)
    (D := 2) (ψ := (827986353987/10000000000000 : ℝ)) half_8_18_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_18_φ1, half_8_18_φ2, half_8_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_18_φ1, half_8_18_φ2, half_8_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_18_φ1, half_8_18_φ2, half_8_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6 half_8_17
    (by simpa only [half_8_18_φ2, show (2:ℝ)*2=4 by norm_num] using half_8_18_hx2)
  exact h.weaken (by norm_num [half_8_18_φ1, half_8_18_φ2, half_8_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_18 : AdmissibleExponent 8 16 (24607155178631/2500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 6) (ψ := (233883574971/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_7_18
    (by simpa only [half_8_18_φ1] using half_8_18_hx1)
  exact admissibleExponent_mono h (by norm_num [half_8_18_φ1, half_8_18_φ2, half_8_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_18_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (990798565309/10000000000000 : ℝ)

private def half_9_18_φ2 : Fin 2 → ℝ := Fin.snoc half_9_18_φ1 (905542185057/10000000000000 : ℝ)

private def half_9_18_φ3 : Fin 3 → ℝ := Fin.snoc half_9_18_φ2 (374658524863/5000000000000 : ℝ)

private theorem half_9_18_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_9_18_φ3) (13610296549517/2500000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_18_φ3 (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_18_hx3 : SourcePowerBound (powerBoxCross 8 6 8 half_9_18_φ3) (13580225694897/2000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 6) (r := 2) (v := 8) (w := 8) (D := 8)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_9_18_φ3 (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_18_hF2 half_8_18 half_8_18
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_18_hx2 : SourcePowerBound (powerBoxCross 8 7 4 half_9_18_φ2) (81316215518553/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (374658524863/5000000000000 : ℝ)) half_9_18_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6 half_8_18
    (by simpa only [half_9_18_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_18_hx3)
  exact h.weaken (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_18_hx1 : SourcePowerBound (powerBoxCross 8 8 2 half_9_18_φ1) (24916781415227/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (905542185057/10000000000000 : ℝ)) half_9_18_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_7_18 half_9_17
    (by simpa only [half_9_18_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_18_hx2)
  exact h.weaken (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_18 : AdmissibleExponent 8 18 (114529104140543/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 7) (ψ := (990798565309/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_8_18
    (by simpa only [half_9_18_φ1] using half_9_18_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_18_φ1, half_9_18_φ2, half_9_18_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_7_19_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (441291542537/5000000000000 : ℝ)

private def half_7_19_φ2 : Fin 2 → ℝ := Fin.snoc half_7_19_φ1 (573782719/7812500000 : ℝ)

private def half_7_19_φ3 : Fin 3 → ℝ := Fin.snoc half_7_19_φ2 (65849809671/2500000000000 : ℝ)

private theorem half_7_19_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_7_19_φ3) (35255545857181/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_19_φ3 (by norm_num [half_7_19_φ1, half_7_19_φ2, half_7_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_19_φ1, half_7_19_φ2, half_7_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_19_φ1, half_7_19_φ2, half_7_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_7_19_φ1, half_7_19_φ2, half_7_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_7_19_hF1 : SourcePowerBound (paddedMoment 8 0 1 8 half_7_19_φ3) (13418515285727/5000000000000 : ℝ) := by
  have h := padded_second_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_7_19_φ3 (by norm_num [half_7_19_φ1, half_7_19_φ2, half_7_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_19_φ1, half_7_19_φ2, half_7_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_19_φ1, half_7_19_φ2, half_7_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_7_19_φ1, half_7_19_φ2, half_7_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_7_19_hx3 : SourcePowerBound (powerBoxCross 8 4 8 half_7_19_φ3) (3323770353479/625000000000 : ℝ) := by
  have h := full_B_cross_power (k := 8) (s := 4) (r := 1) (v := 2) (t := 7) (D := 8)
    (a := (5/14 : ℝ)) (b := (1/14 : ℝ)) (c := (4/7 : ℝ))
    (by norm_num) half_7_19_φ3 (by norm_num [half_7_19_φ1, half_7_19_φ2, half_7_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_19_φ1, half_7_19_φ2, half_7_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_7_19_hF1 half_7_19_hF2 half_7_18
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_7_19_φ1, half_7_19_φ2, half_7_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_19_hx2 : SourcePowerBound (powerBoxCross 8 5 4 half_7_19_φ2) (3029603100961/500000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 5) (u := 3) (t := 6)
    (D := 4) (ψ := (65849809671/2500000000000 : ℝ)) half_7_19_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_7_19_φ1, half_7_19_φ2, half_7_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_19_φ1, half_7_19_φ2, half_7_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_7_19_φ1, half_7_19_φ2, half_7_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_4 SeedCompletionEven8SecondSeeds.degree8_half_6
    (by simpa only [half_7_19_φ3, show (2:ℝ)*4=8 by norm_num] using half_7_19_hx3)
  exact h.weaken (by norm_num [half_7_19_φ1, half_7_19_φ2, half_7_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_19_hx1 : SourcePowerBound (powerBoxCross 8 6 2 half_7_19_φ1) (73397577090513/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 6) (u := 4) (t := 7)
    (D := 2) (ψ := (573782719/7812500000 : ℝ)) half_7_19_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_7_19_φ1, half_7_19_φ2, half_7_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_7_19_φ1, half_7_19_φ2, half_7_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_7_19_φ1, half_7_19_φ2, half_7_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_5 half_7_18
    (by simpa only [half_7_19_φ2, show (2:ℝ)*2=4 by norm_num] using half_7_19_hx2)
  exact h.weaken (by norm_num [half_7_19_φ1, half_7_19_φ2, half_7_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_7_19 : AdmissibleExponent 8 14 (83105991026327/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 5) (ψ := (441291542537/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6
    (by simpa only [half_7_19_φ1] using half_7_19_hx1)
  exact admissibleExponent_mono h (by norm_num [half_7_19_φ1, half_7_19_φ2, half_7_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_8_19_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (116941787059/1250000000000 : ℝ)

private def half_8_19_φ2 : Fin 2 → ℝ := Fin.snoc half_8_19_φ1 (827986353567/10000000000000 : ℝ)

private def half_8_19_φ3 : Fin 3 → ℝ := Fin.snoc half_8_19_φ2 (558045659499/10000000000000 : ℝ)

private theorem half_8_19_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_8_19_φ3) (30623553749851/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_8_19_φ3 (by norm_num [half_8_19_φ1, half_8_19_φ2, half_8_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_19_φ1, half_8_19_φ2, half_8_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_19_φ1, half_8_19_φ2, half_8_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_8_19_φ1, half_8_19_φ2, half_8_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_8_19_hx3 : SourcePowerBound (powerBoxCross 8 5 8 half_8_19_φ3) (60380064102063/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 5) (r := 2) (v := 6) (w := 7) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_8_19_φ3 (by norm_num [half_8_19_φ1, half_8_19_φ2, half_8_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_19_φ1, half_8_19_φ2, half_8_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_8_19_hF2 SeedCompletionEven8SecondSeeds.degree8_half_6 half_7_19
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_8_19_φ1, half_8_19_φ2, half_8_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_19_hx2 : SourcePowerBound (powerBoxCross 8 6 4 half_8_19_φ2) (884424427387/125000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 6) (u := 4) (t := 7)
    (D := 4) (ψ := (558045659499/10000000000000 : ℝ)) half_8_19_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_19_φ1, half_8_19_φ2, half_8_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_19_φ1, half_8_19_φ2, half_8_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_19_φ1, half_8_19_φ2, half_8_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_5 half_7_19
    (by simpa only [half_8_19_φ3, show (2:ℝ)*4=8 by norm_num] using half_8_19_hx3)
  exact h.weaken (by norm_num [half_8_19_φ1, half_8_19_φ2, half_8_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_19_hx1 : SourcePowerBound (powerBoxCross 8 7 2 half_8_19_φ1) (17253334967613/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 7) (u := 5) (t := 8)
    (D := 2) (ψ := (827986353567/10000000000000 : ℝ)) half_8_19_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_8_19_φ1, half_8_19_φ2, half_8_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_8_19_φ1, half_8_19_φ2, half_8_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_8_19_φ1, half_8_19_φ2, half_8_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6 half_8_18
    (by simpa only [half_8_19_φ2, show (2:ℝ)*2=4 by norm_num] using half_8_19_hx2)
  exact h.weaken (by norm_num [half_8_19_φ1, half_8_19_φ2, half_8_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_8_19 : AdmissibleExponent 8 16 (98428620692201/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 6) (ψ := (116941787059/1250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_7_19
    (by simpa only [half_8_19_φ1] using half_8_19_hx1)
  exact admissibleExponent_mono h (by norm_num [half_8_19_φ1, half_8_19_φ2, half_8_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private def half_9_19_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (19815970809/200000000000 : ℝ)

private def half_9_19_φ2 : Fin 2 → ℝ := Fin.snoc half_9_19_φ1 (905542182193/10000000000000 : ℝ)

private def half_9_19_φ3 : Fin 3 → ℝ := Fin.snoc half_9_19_φ2 (749317042899/10000000000000 : ℝ)

private theorem half_9_19_hF2 : SourcePowerBound (paddedMoment 8 0 2 8 half_9_19_φ3) (27220593461809/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 8) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_19_φ3 (by norm_num [half_9_19_φ1, half_9_19_φ2, half_9_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_19_φ1, half_9_19_φ2, half_9_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_19_φ1, half_9_19_φ2, half_9_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_19_φ1, half_9_19_φ2, half_9_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

private theorem half_9_19_hx3 : SourcePowerBound (powerBoxCross 8 6 8 half_9_19_φ3) (67901128898613/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 8) (s := 6) (r := 2) (v := 8) (w := 8) (D := 8)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_9_19_φ3 (by norm_num [half_9_19_φ1, half_9_19_φ2, half_9_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_19_φ1, half_9_19_φ2, half_9_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_19_hF2 half_8_19 half_8_19
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_19_φ1, half_9_19_φ2, half_9_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_19_hx2 : SourcePowerBound (powerBoxCross 8 7 4 half_9_19_φ2) (81316215917491/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (749317042899/10000000000000 : ℝ)) half_9_19_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_19_φ1, half_9_19_φ2, half_9_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_19_φ1, half_9_19_φ2, half_9_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_19_φ1, half_9_19_φ2, half_9_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven8SecondSeeds.degree8_half_6 half_8_19
    (by simpa only [half_9_19_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_19_hx3)
  exact h.weaken (by norm_num [half_9_19_φ1, half_9_19_φ2, half_9_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_19_hx1 : SourcePowerBound (powerBoxCross 8 8 2 half_9_19_φ1) (49833562930311/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 8) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (905542182193/10000000000000 : ℝ)) half_9_19_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_19_φ1, half_9_19_φ2, half_9_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_19_φ1, half_9_19_φ2, half_9_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_19_φ1, half_9_19_φ2, half_9_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_7_19 half_9_18
    (by simpa only [half_9_19_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_19_hx2)
  exact h.weaken (by norm_num [half_9_19_φ1, half_9_19_φ2, half_9_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

private theorem half_9_19 : AdmissibleExponent 8 18 (28632275991843/2500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 8) (s := 7) (ψ := (19815970809/200000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_8_19
    (by simpa only [half_9_19_φ1] using half_9_19_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_19_φ1, half_9_19_φ2, half_9_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem degree8_half_7 : AdmissibleExponent 8 14 (83105991026327/10000000000000 : ℝ) := half_7_19

theorem source8_entry_7 : AdmissibleExponent 8 14 (Certificate.source8[7]! : ℝ) := by
  apply admissibleExponent_mono degree8_half_7
  norm_num [Certificate.source8,Certificate.Q]

#print axioms source8_entry_7

theorem degree8_half_8 : AdmissibleExponent 8 16 (98428620692201/10000000000000 : ℝ) := half_8_19

theorem source8_entry_8 : AdmissibleExponent 8 16 (Certificate.source8[8]! : ℝ) := by
  apply admissibleExponent_mono degree8_half_8
  norm_num [Certificate.source8,Certificate.Q]

#print axioms source8_entry_8

theorem degree8_half_9 : AdmissibleExponent 8 18 (28632275991843/2500000000000 : ℝ) := half_9_19

theorem source8_entry_9 : AdmissibleExponent 8 18 (Certificate.source8[9]! : ℝ) := by
  apply admissibleExponent_mono degree8_half_9
  norm_num [Certificate.source8,Certificate.Q]

#print axioms source8_entry_9

end Waring.SeedCompletionHigher8SimpleSeeds
