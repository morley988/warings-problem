import Waring.SeedCompletionHigher18SimpleSeedsC18

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionHigher18SimpleSeeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges

def half_9_19_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (42979853791/1250000000000 : ℝ)

def half_9_19_φ2 : Fin 2 → ℝ := Fin.snoc half_9_19_φ1 (308345143257/10000000000000 : ℝ)

def half_9_19_φ3 : Fin 3 → ℝ := Fin.snoc half_9_19_φ2 (67222953979/5000000000000 : ℝ)

theorem half_9_19_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_9_19_φ3) (69881876041307/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_19_φ3 (by norm_num [half_9_19_φ1, half_9_19_φ2, half_9_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_19_φ1, half_9_19_φ2, half_9_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_19_φ1, half_9_19_φ2, half_9_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_19_φ1, half_9_19_φ2, half_9_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_19_hF1 : SourcePowerBound (paddedMoment 18 0 1 8 half_9_19_φ3) (26627292013769/10000000000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_19_φ3 (by norm_num [half_9_19_φ1, half_9_19_φ2, half_9_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_19_φ1, half_9_19_φ2, half_9_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_19_φ1, half_9_19_φ2, half_9_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_19_φ1, half_9_19_φ2, half_9_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_19_hx3 : SourcePowerBound (powerBoxCross 18 6 8 half_9_19_φ3) (38496518554211/5000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 6) (r := 1) (v := 2) (t := 10) (D := 8)
    (a := (3/10 : ℝ)) (b := (1/10 : ℝ)) (c := (3/5 : ℝ))
    (by norm_num) half_9_19_φ3 (by norm_num [half_9_19_φ1, half_9_19_φ2, half_9_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_19_φ1, half_9_19_φ2, half_9_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_19_hF1 half_9_19_hF2 half_10_18
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_19_φ1, half_9_19_φ2, half_9_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_19_hx2 : SourcePowerBound (powerBoxCross 18 7 4 half_9_19_φ2) (42134710898607/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (67222953979/5000000000000 : ℝ)) half_9_19_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_19_φ1, half_9_19_φ2, half_9_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_19_φ1, half_9_19_φ2, half_9_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_19_φ1, half_9_19_φ2, half_9_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_6 SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_19_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_19_hx3)
  exact h.weaken (by norm_num [half_9_19_φ1, half_9_19_φ2, half_9_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_19_hx1 : SourcePowerBound (powerBoxCross 18 8 2 half_9_19_φ1) (753398384371/80000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (308345143257/10000000000000 : ℝ)) half_9_19_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_19_φ1, half_9_19_φ2, half_9_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_19_φ1, half_9_19_φ2, half_9_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_19_φ1, half_9_19_φ2, half_9_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_18
    (by simpa only [half_9_19_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_19_hx2)
  exact h.weaken (by norm_num [half_9_19_φ1, half_9_19_φ2, half_9_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_19 : AdmissibleExponent 18 18 (19866476100259/2000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 7) (ψ := (42979853791/1250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_19_φ1] using half_9_19_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_19_φ1, half_9_19_φ2, half_9_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_10_19_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (353748845761/10000000000000 : ℝ)

def half_10_19_φ2 : Fin 2 → ℝ := Fin.snoc half_10_19_φ1 (329256566551/10000000000000 : ℝ)

def half_10_19_φ3 : Fin 3 → ℝ := Fin.snoc half_10_19_φ2 (28742347607/1250000000000 : ℝ)

theorem half_10_19_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_10_19_φ3) (3964990384277/625000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_19_φ3 (by norm_num [half_10_19_φ1, half_10_19_φ2, half_10_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_19_φ1, half_10_19_φ2, half_10_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_19_φ1, half_10_19_φ2, half_10_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_10_19_φ1, half_10_19_φ2, half_10_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_10_19_hx3 : SourcePowerBound (powerBoxCross 18 7 8 half_10_19_φ3) (86477914183947/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 7) (r := 2) (v := 9) (w := 10) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_10_19_φ3 (by norm_num [half_10_19_φ1, half_10_19_φ2, half_10_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_19_φ1, half_10_19_φ2, half_10_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_19_hF2 half_9_19 half_10_18
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_19_φ1, half_10_19_φ2, half_10_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_19_hx2 : SourcePowerBound (powerBoxCross 18 8 4 half_10_19_φ2) (95201975738523/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (28742347607/1250000000000 : ℝ)) half_10_19_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_19_φ1, half_10_19_φ2, half_10_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_19_φ1, half_10_19_φ2, half_10_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_19_φ1, half_10_19_φ2, half_10_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_19
    (by simpa only [half_10_19_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_19_hx3)
  exact h.weaken (by norm_num [half_10_19_φ1, half_10_19_φ2, half_10_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_19_hx1 : SourcePowerBound (powerBoxCross 18 9 2 half_10_19_φ1) (53086128926079/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (329256566551/10000000000000 : ℝ)) half_10_19_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_19_φ1, half_10_19_φ2, half_10_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_19_φ1, half_10_19_φ2, half_10_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_19_φ1, half_10_19_φ2, half_10_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_18
    (by simpa only [half_10_19_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_19_hx2)
  exact h.weaken (by norm_num [half_10_19_φ1, half_10_19_φ2, half_10_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_19 : AdmissibleExponent 18 20 (22437197646019/2000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 8) (ψ := (353748845761/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_9_19
    (by simpa only [half_10_19_φ1] using half_10_19_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_19_φ1, half_10_19_φ2, half_10_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_11_19_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (364748133577/10000000000000 : ℝ)

def half_11_19_φ2 : Fin 2 → ℝ := Fin.snoc half_11_19_φ1 (346394857241/10000000000000 : ℝ)

def half_11_19_φ3 : Fin 3 → ℝ := Fin.snoc half_11_19_φ2 (147364245623/5000000000000 : ℝ)

theorem half_11_19_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_11_19_φ3) (3668784650921/625000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_19_φ3 (by norm_num [half_11_19_φ1, half_11_19_φ2, half_11_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_19_φ1, half_11_19_φ2, half_11_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_19_φ1, half_11_19_φ2, half_11_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_19_φ1, half_11_19_φ2, half_11_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_11_19_hx3 : SourcePowerBound (powerBoxCross 18 8 8 half_11_19_φ3) (24072188027359/2500000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 8) (r := 2) (v := 10) (w := 11) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_11_19_φ3 (by norm_num [half_11_19_φ1, half_11_19_φ2, half_11_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_19_φ1, half_11_19_φ2, half_11_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_19_hF2 half_10_19 half_11_18
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_19_φ1, half_11_19_φ2, half_11_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_19_hx2 : SourcePowerBound (powerBoxCross 18 9 4 half_11_19_φ2) (26603526118067/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (147364245623/5000000000000 : ℝ)) half_11_19_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_19_φ1, half_11_19_φ2, half_11_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_19_φ1, half_11_19_φ2, half_11_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_19_φ1, half_11_19_φ2, half_11_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_19
    (by simpa only [half_11_19_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_19_hx3)
  exact h.weaken (by norm_num [half_11_19_φ1, half_11_19_φ2, half_11_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_19_hx1 : SourcePowerBound (powerBoxCross 18 10 2 half_11_19_φ1) (59229386690821/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (346394857241/10000000000000 : ℝ)) half_11_19_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_19_φ1, half_11_19_φ2, half_11_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_19_φ1, half_11_19_φ2, half_11_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_19_φ1, half_11_19_φ2, half_11_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_19 half_11_18
    (by simpa only [half_11_19_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_19_hx2)
  exact h.weaken (by norm_num [half_11_19_φ1, half_11_19_φ2, half_11_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_19 : AdmissibleExponent 18 22 (25077797583921/2000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 9) (ψ := (364748133577/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_10_19
    (by simpa only [half_11_19_φ1] using half_11_19_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_19_φ1, half_11_19_φ2, half_11_19_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_12_19_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (374941954253/10000000000000 : ℝ)

def half_12_19_φ2 : Fin 2 → ℝ := Fin.snoc half_12_19_φ1 (360586864607/10000000000000 : ℝ)

def half_12_19_φ3 : Fin 3 → ℝ := Fin.snoc half_12_19_φ2 (329430069621/10000000000000 : ℝ)

def half_12_19_φ4 : Fin 4 → ℝ := Fin.snoc half_12_19_φ3 (212907346943/10000000000000 : ℝ)

theorem half_12_19_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_12_19_φ4) (2338400687293/312500000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_19_φ4 (by norm_num [half_12_19_φ1, half_12_19_φ2, half_12_19_φ3, half_12_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_19_φ1, half_12_19_φ2, half_12_19_φ3, half_12_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_19_φ1, half_12_19_φ2, half_12_19_φ3, half_12_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_19_φ1, half_12_19_φ2, half_12_19_φ3, half_12_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_19_hF1 : SourcePowerBound (paddedMoment 18 0 1 16 half_12_19_φ4) (883633562431/312500000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_19_φ4 (by norm_num [half_12_19_φ1, half_12_19_φ2, half_12_19_φ3, half_12_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_19_φ1, half_12_19_φ2, half_12_19_φ3, half_12_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_19_φ1, half_12_19_φ2, half_12_19_φ3, half_12_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_19_φ1, half_12_19_φ2, half_12_19_φ3, half_12_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_19_hx4 : SourcePowerBound (powerBoxCross 18 8 16 half_12_19_φ4) (48915355098819/5000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 8) (r := 1) (v := 2) (t := 11) (D := 16)
    (a := (1/22 : ℝ)) (b := (5/22 : ℝ)) (c := (8/11 : ℝ))
    (by norm_num) half_12_19_φ4 (by norm_num [half_12_19_φ1, half_12_19_φ2, half_12_19_φ3, half_12_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_19_φ1, half_12_19_φ2, half_12_19_φ3, half_12_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_19_hF1 half_12_19_hF2 half_11_19
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_19_φ1, half_12_19_φ2, half_12_19_φ3, half_12_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_19_hx3 : SourcePowerBound (powerBoxCross 18 9 8 half_12_19_φ3) (53289665248709/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (212907346943/10000000000000 : ℝ)) half_12_19_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_19_φ1, half_12_19_φ2, half_12_19_φ3, half_12_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_19_φ1, half_12_19_φ2, half_12_19_φ3, half_12_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_19_φ1, half_12_19_φ2, half_12_19_φ3, half_12_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_19
    (by simpa only [half_12_19_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_19_hx4)
  exact h.weaken (by norm_num [half_12_19_φ1, half_12_19_φ2, half_12_19_φ3, half_12_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_19_hx2 : SourcePowerBound (powerBoxCross 18 10 4 half_12_19_φ2) (117920959130853/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (329430069621/10000000000000 : ℝ)) half_12_19_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_19_φ1, half_12_19_φ2, half_12_19_φ3, half_12_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_19_φ1, half_12_19_φ2, half_12_19_φ3, half_12_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_19_φ1, half_12_19_φ2, half_12_19_φ3, half_12_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_19 half_11_19
    (by simpa only [half_12_19_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_19_hx3)
  exact h.weaken (by norm_num [half_12_19_φ1, half_12_19_φ2, half_12_19_φ3, half_12_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_19_hx1 : SourcePowerBound (powerBoxCross 18 11 2 half_12_19_φ1) (131062570656627/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (360586864607/10000000000000 : ℝ)) half_12_19_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_19_φ1, half_12_19_φ2, half_12_19_φ3, half_12_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_19_φ1, half_12_19_φ2, half_12_19_φ3, half_12_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_19_φ1, half_12_19_φ2, half_12_19_φ3, half_12_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_19 half_12_18
    (by simpa only [half_12_19_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_19_hx2)
  exact h.weaken (by norm_num [half_12_19_φ1, half_12_19_φ2, half_12_19_φ3, half_12_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_19 : AdmissibleExponent 18 24 (6946817584797/500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 10) (ψ := (374941954253/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_11_19
    (by simpa only [half_12_19_φ1] using half_12_19_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_19_φ1, half_12_19_φ2, half_12_19_φ3, half_12_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_13_19_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (24037775543/625000000000 : ℝ)

def half_13_19_φ2 : Fin 2 → ℝ := Fin.snoc half_13_19_φ1 (371968405573/10000000000000 : ℝ)

def half_13_19_φ3 : Fin 3 → ℝ := Fin.snoc half_13_19_φ2 (349893155149/10000000000000 : ℝ)

def half_13_19_φ4 : Fin 4 → ℝ := Fin.snoc half_13_19_φ3 (141656631887/5000000000000 : ℝ)

theorem half_13_19_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_13_19_φ4) (2160039347113/312500000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_19_φ4 (by norm_num [half_13_19_φ1, half_13_19_φ2, half_13_19_φ3, half_13_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_19_φ1, half_13_19_φ2, half_13_19_φ3, half_13_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_19_φ1, half_13_19_φ2, half_13_19_φ3, half_13_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_19_φ1, half_13_19_φ2, half_13_19_φ3, half_13_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_13_19_hx4 : SourcePowerBound (powerBoxCross 18 9 16 half_13_19_φ4) (107000764324757/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 16)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_13_19_φ4 (by norm_num [half_13_19_φ1, half_13_19_φ2, half_13_19_φ3, half_13_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_19_φ1, half_13_19_φ2, half_13_19_φ3, half_13_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_19_hF2 half_12_19 half_12_19
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_19_φ1, half_13_19_φ2, half_13_19_φ3, half_13_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_19_hx3 : SourcePowerBound (powerBoxCross 18 10 8 half_13_19_φ3) (23452229144137/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (141656631887/5000000000000 : ℝ)) half_13_19_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_19_φ1, half_13_19_φ2, half_13_19_φ3, half_13_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_19_φ1, half_13_19_φ2, half_13_19_φ3, half_13_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_19_φ1, half_13_19_φ2, half_13_19_φ3, half_13_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_19 half_11_19
    (by simpa only [half_13_19_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_19_hx4)
  exact h.weaken (by norm_num [half_13_19_φ1, half_13_19_φ2, half_13_19_φ3, half_13_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_19_hx2 : SourcePowerBound (powerBoxCross 18 11 4 half_13_19_φ2) (64868045715361/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (349893155149/10000000000000 : ℝ)) half_13_19_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_19_φ1, half_13_19_φ2, half_13_19_φ3, half_13_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_19_φ1, half_13_19_φ2, half_13_19_φ3, half_13_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_19_φ1, half_13_19_φ2, half_13_19_φ3, half_13_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_19 half_12_19
    (by simpa only [half_13_19_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_19_hx3)
  exact h.weaken (by norm_num [half_13_19_φ1, half_13_19_φ2, half_13_19_φ3, half_13_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_19_hx1 : SourcePowerBound (powerBoxCross 18 12 2 half_13_19_φ1) (71988701382853/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (371968405573/10000000000000 : ℝ)) half_13_19_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_19_φ1, half_13_19_φ2, half_13_19_φ3, half_13_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_19_φ1, half_13_19_φ2, half_13_19_φ3, half_13_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_19_φ1, half_13_19_φ2, half_13_19_φ3, half_13_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_19 half_13_18
    (by simpa only [half_13_19_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_19_hx2)
  exact h.weaken (by norm_num [half_13_19_φ1, half_13_19_φ2, half_13_19_φ3, half_13_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_19 : AdmissibleExponent 18 26 (15282330416553/1000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 11) (ψ := (24037775543/625000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_12_19
    (by simpa only [half_13_19_φ1] using half_13_19_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_19_φ1, half_13_19_φ2, half_13_19_φ3, half_13_19_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_14_19_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (98590168267/2500000000000 : ℝ)

def half_14_19_φ2 : Fin 2 → ℝ := Fin.snoc half_14_19_φ1 (382996727883/10000000000000 : ℝ)

def half_14_19_φ3 : Fin 3 → ℝ := Fin.snoc half_14_19_φ2 (91815202389/2500000000000 : ℝ)

def half_14_19_φ4 : Fin 4 → ℝ := Fin.snoc half_14_19_φ3 (66423149083/2000000000000 : ℝ)

def half_14_19_φ5 : Fin 5 → ℝ := Fin.snoc half_14_19_φ4 (205580725177/10000000000000 : ℝ)

theorem half_14_19_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_14_19_φ5) (84201951263951/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_14_19_φ5 (by norm_num [half_14_19_φ1, half_14_19_φ2, half_14_19_φ3, half_14_19_φ4, half_14_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_19_φ1, half_14_19_φ2, half_14_19_φ3, half_14_19_φ4, half_14_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_19_φ1, half_14_19_φ2, half_14_19_φ3, half_14_19_φ4, half_14_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_14_19_φ1, half_14_19_φ2, half_14_19_φ3, half_14_19_φ4, half_14_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_14_19_hx5 : SourcePowerBound (powerBoxCross 18 9 32 half_14_19_φ5) (26930662943303/2500000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_14_19_φ5 (by norm_num [half_14_19_φ1, half_14_19_φ2, half_14_19_φ3, half_14_19_φ4, half_14_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_19_φ1, half_14_19_φ2, half_14_19_φ3, half_14_19_φ4, half_14_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_19_hF2 half_12_19 half_12_19
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_19_φ1, half_14_19_φ2, half_14_19_φ3, half_14_19_φ4, half_14_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_19_hx4 : SourcePowerBound (powerBoxCross 18 10 16 half_14_19_φ4) (116492708577099/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (205580725177/10000000000000 : ℝ)) half_14_19_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_19_φ1, half_14_19_φ2, half_14_19_φ3, half_14_19_φ4, half_14_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_19_φ1, half_14_19_φ2, half_14_19_φ3, half_14_19_φ4, half_14_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_19_φ1, half_14_19_φ2, half_14_19_φ3, half_14_19_φ4, half_14_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_19 half_11_19
    (by simpa only [half_14_19_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_19_hx5)
  exact h.weaken (by norm_num [half_14_19_φ1, half_14_19_φ2, half_14_19_φ3, half_14_19_φ4, half_14_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_19_hx3 : SourcePowerBound (powerBoxCross 18 11 8 half_14_19_φ3) (16023615127003/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (66423149083/2000000000000 : ℝ)) half_14_19_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_19_φ1, half_14_19_φ2, half_14_19_φ3, half_14_19_φ4, half_14_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_19_φ1, half_14_19_φ2, half_14_19_φ3, half_14_19_φ4, half_14_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_19_φ1, half_14_19_φ2, half_14_19_φ3, half_14_19_φ4, half_14_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_19 half_12_19
    (by simpa only [half_14_19_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_19_hx4)
  exact h.weaken (by norm_num [half_14_19_φ1, half_14_19_φ2, half_14_19_φ3, half_14_19_φ4, half_14_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_19_hx2 : SourcePowerBound (powerBoxCross 18 12 4 half_14_19_φ2) (141814896856489/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (91815202389/2500000000000 : ℝ)) half_14_19_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_19_φ1, half_14_19_φ2, half_14_19_φ3, half_14_19_φ4, half_14_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_19_φ1, half_14_19_φ2, half_14_19_φ3, half_14_19_φ4, half_14_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_19_φ1, half_14_19_φ2, half_14_19_φ3, half_14_19_φ4, half_14_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_19 half_13_19
    (by simpa only [half_14_19_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_19_hx3)
  exact h.weaken (by norm_num [half_14_19_φ1, half_14_19_φ2, half_14_19_φ3, half_14_19_φ4, half_14_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_19_hx1 : SourcePowerBound (powerBoxCross 18 13 2 half_14_19_φ1) (157190914729489/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (382996727883/10000000000000 : ℝ)) half_14_19_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_19_φ1, half_14_19_φ2, half_14_19_φ3, half_14_19_φ4, half_14_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_19_φ1, half_14_19_φ2, half_14_19_φ3, half_14_19_φ4, half_14_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_19_φ1, half_14_19_φ2, half_14_19_φ3, half_14_19_φ4, half_14_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_19 half_14_18
    (by simpa only [half_14_19_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_19_hx2)
  exact h.weaken (by norm_num [half_14_19_φ1, half_14_19_φ2, half_14_19_φ3, half_14_19_φ4, half_14_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_19 : AdmissibleExponent 18 28 (167049931556189/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 12) (ψ := (98590168267/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_13_19
    (by simpa only [half_14_19_φ1] using half_14_19_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_19_φ1, half_14_19_φ2, half_14_19_φ3, half_14_19_φ4, half_14_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_15_19_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (201818801891/5000000000000 : ℝ)

def half_15_19_φ2 : Fin 2 → ℝ := Fin.snoc half_15_19_φ1 (196493772893/5000000000000 : ℝ)

def half_15_19_φ3 : Fin 3 → ℝ := Fin.snoc half_15_19_φ2 (94864378787/2500000000000 : ℝ)

def half_15_19_φ4 : Fin 4 → ℝ := Fin.snoc half_15_19_φ3 (44403133099/1250000000000 : ℝ)

def half_15_19_φ5 : Fin 5 → ℝ := Fin.snoc half_15_19_φ4 (28429073381/1000000000000 : ℝ)

theorem half_15_19_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_15_19_φ5) (38702239185391/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_15_19_φ5 (by norm_num [half_15_19_φ1, half_15_19_φ2, half_15_19_φ3, half_15_19_φ4, half_15_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_19_φ1, half_15_19_φ2, half_15_19_φ3, half_15_19_φ4, half_15_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_19_φ1, half_15_19_φ2, half_15_19_φ3, half_15_19_φ4, half_15_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_15_19_φ1, half_15_19_φ2, half_15_19_φ3, half_15_19_φ4, half_15_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_15_19_hx5 : SourcePowerBound (powerBoxCross 18 10 32 half_15_19_φ5) (116069576778633/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_15_19_φ5 (by norm_num [half_15_19_φ1, half_15_19_φ2, half_15_19_φ3, half_15_19_φ4, half_15_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_19_φ1, half_15_19_φ2, half_15_19_φ3, half_15_19_φ4, half_15_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_15_19_hF2 half_13_19 half_14_19
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_19_φ1, half_15_19_φ2, half_15_19_φ3, half_15_19_φ4, half_15_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_19_hx4 : SourcePowerBound (powerBoxCross 18 11 16 half_15_19_φ4) (63274947522291/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (28429073381/1000000000000 : ℝ)) half_15_19_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_19_φ1, half_15_19_φ2, half_15_19_φ3, half_15_19_φ4, half_15_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_19_φ1, half_15_19_φ2, half_15_19_φ3, half_15_19_φ4, half_15_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_19_φ1, half_15_19_φ2, half_15_19_φ3, half_15_19_φ4, half_15_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_19 half_12_19
    (by simpa only [half_15_19_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_19_hx5)
  exact h.weaken (by norm_num [half_15_19_φ1, half_15_19_φ2, half_15_19_φ3, half_15_19_φ4, half_15_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_19_hx3 : SourcePowerBound (powerBoxCross 18 12 8 half_15_19_φ3) (139433118195601/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (44403133099/1250000000000 : ℝ)) half_15_19_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_19_φ1, half_15_19_φ2, half_15_19_φ3, half_15_19_φ4, half_15_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_19_φ1, half_15_19_φ2, half_15_19_φ3, half_15_19_φ4, half_15_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_19_φ1, half_15_19_φ2, half_15_19_φ3, half_15_19_φ4, half_15_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_19 half_13_19
    (by simpa only [half_15_19_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_19_hx4)
  exact h.weaken (by norm_num [half_15_19_φ1, half_15_19_φ2, half_15_19_φ3, half_15_19_φ4, half_15_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_19_hx2 : SourcePowerBound (powerBoxCross 18 13 4 half_15_19_φ2) (77090081846603/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (94864378787/2500000000000 : ℝ)) half_15_19_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_19_φ1, half_15_19_φ2, half_15_19_φ3, half_15_19_φ4, half_15_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_19_φ1, half_15_19_φ2, half_15_19_φ3, half_15_19_φ4, half_15_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_19_φ1, half_15_19_φ2, half_15_19_φ3, half_15_19_φ4, half_15_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_19 half_14_19
    (by simpa only [half_15_19_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_19_hx3)
  exact h.weaken (by norm_num [half_15_19_φ1, half_15_19_φ2, half_15_19_φ3, half_15_19_φ4, half_15_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_19_hx1 : SourcePowerBound (powerBoxCross 18 14 2 half_15_19_φ1) (5334712679733/312500000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (196493772893/5000000000000 : ℝ)) half_15_19_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_19_φ1, half_15_19_φ2, half_15_19_φ3, half_15_19_φ4, half_15_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_19_φ1, half_15_19_φ2, half_15_19_φ3, half_15_19_φ4, half_15_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_19_φ1, half_15_19_φ2, half_15_19_φ3, half_15_19_φ4, half_15_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_19 half_15_18
    (by simpa only [half_15_19_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_19_hx2)
  exact h.weaken (by norm_num [half_15_19_φ1, half_15_19_φ2, half_15_19_φ3, half_15_19_φ4, half_15_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_19 : AdmissibleExponent 18 30 (18160902105357/1000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 13) (ψ := (201818801891/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_14_19
    (by simpa only [half_15_19_φ1] using half_15_19_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_19_φ1, half_15_19_φ2, half_15_19_φ3, half_15_19_φ4, half_15_19_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_16_19_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (206444242957/5000000000000 : ℝ)

def half_16_19_φ2 : Fin 2 → ℝ := Fin.snoc half_16_19_φ1 (201347204957/5000000000000 : ℝ)

def half_16_19_φ3 : Fin 3 → ℝ := Fin.snoc half_16_19_φ2 (78219461019/2000000000000 : ℝ)

def half_16_19_φ4 : Fin 4 → ℝ := Fin.snoc half_16_19_φ3 (374102461767/10000000000000 : ℝ)

def half_16_19_φ5 : Fin 5 → ℝ := Fin.snoc half_16_19_φ4 (168150696853/5000000000000 : ℝ)

def half_16_19_φ6 : Fin 6 → ℝ := Fin.snoc half_16_19_φ5 (208224580543/10000000000000 : ℝ)

theorem half_16_19_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_16_19_φ6) (91609259516111/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_16_19_φ6 (by norm_num [half_16_19_φ1, half_16_19_φ2, half_16_19_φ3, half_16_19_φ4, half_16_19_φ5, half_16_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_19_φ1, half_16_19_φ2, half_16_19_φ3, half_16_19_φ4, half_16_19_φ5, half_16_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_19_φ1, half_16_19_φ2, half_16_19_φ3, half_16_19_φ4, half_16_19_φ5, half_16_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_16_19_φ1, half_16_19_φ2, half_16_19_φ3, half_16_19_φ4, half_16_19_φ5, half_16_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_16_19_hx6 : SourcePowerBound (powerBoxCross 18 10 64 half_16_19_φ6) (57980399439501/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_16_19_φ6 (by norm_num [half_16_19_φ1, half_16_19_φ2, half_16_19_φ3, half_16_19_φ4, half_16_19_φ5, half_16_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_19_φ1, half_16_19_φ2, half_16_19_φ3, half_16_19_φ4, half_16_19_φ5, half_16_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_16_19_hF2 half_13_19 half_14_19
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_19_φ1, half_16_19_φ2, half_16_19_φ3, half_16_19_φ4, half_16_19_φ5, half_16_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_19_hx5 : SourcePowerBound (powerBoxCross 18 11 32 half_16_19_φ5) (62406930544381/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 11) (u := 9) (t := 12)
    (D := 32) (ψ := (208224580543/10000000000000 : ℝ)) half_16_19_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_19_φ1, half_16_19_φ2, half_16_19_φ3, half_16_19_φ4, half_16_19_φ5, half_16_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_19_φ1, half_16_19_φ2, half_16_19_φ3, half_16_19_φ4, half_16_19_φ5, half_16_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_19_φ1, half_16_19_φ2, half_16_19_φ3, half_16_19_φ4, half_16_19_φ5, half_16_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_19 half_12_19
    (by simpa only [half_16_19_φ6, show (2:ℝ)*32=64 by norm_num] using half_16_19_hx6)
  exact h.weaken (by norm_num [half_16_19_φ1, half_16_19_φ2, half_16_19_φ3, half_16_19_φ4, half_16_19_φ5, half_16_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_19_hx4 : SourcePowerBound (powerBoxCross 18 12 16 half_16_19_φ4) (136834073144201/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (168150696853/5000000000000 : ℝ)) half_16_19_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_19_φ1, half_16_19_φ2, half_16_19_φ3, half_16_19_φ4, half_16_19_φ5, half_16_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_19_φ1, half_16_19_φ2, half_16_19_φ3, half_16_19_φ4, half_16_19_φ5, half_16_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_19_φ1, half_16_19_φ2, half_16_19_φ3, half_16_19_φ4, half_16_19_φ5, half_16_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_19 half_13_19
    (by simpa only [half_16_19_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_19_hx5)
  exact h.weaken (by norm_num [half_16_19_φ1, half_16_19_φ2, half_16_19_φ3, half_16_19_φ4, half_16_19_φ5, half_16_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_19_hx3 : SourcePowerBound (powerBoxCross 18 13 8 half_16_19_φ3) (150908606703951/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (374102461767/10000000000000 : ℝ)) half_16_19_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_19_φ1, half_16_19_φ2, half_16_19_φ3, half_16_19_φ4, half_16_19_φ5, half_16_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_19_φ1, half_16_19_φ2, half_16_19_φ3, half_16_19_φ4, half_16_19_φ5, half_16_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_19_φ1, half_16_19_φ2, half_16_19_φ3, half_16_19_φ4, half_16_19_φ5, half_16_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_19 half_14_19
    (by simpa only [half_16_19_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_19_hx4)
  exact h.weaken (by norm_num [half_16_19_φ1, half_16_19_φ2, half_16_19_φ3, half_16_19_φ4, half_16_19_φ5, half_16_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_19_hx2 : SourcePowerBound (powerBoxCross 18 14 4 half_16_19_φ2) (166809215012943/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (78219461019/2000000000000 : ℝ)) half_16_19_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_19_φ1, half_16_19_φ2, half_16_19_φ3, half_16_19_φ4, half_16_19_φ5, half_16_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_19_φ1, half_16_19_φ2, half_16_19_φ3, half_16_19_φ4, half_16_19_φ5, half_16_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_19_φ1, half_16_19_φ2, half_16_19_φ3, half_16_19_φ4, half_16_19_φ5, half_16_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_19 half_15_19
    (by simpa only [half_16_19_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_19_hx3)
  exact h.weaken (by norm_num [half_16_19_φ1, half_16_19_φ2, half_16_19_φ3, half_16_19_φ4, half_16_19_φ5, half_16_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_19_hx1 : SourcePowerBound (powerBoxCross 18 15 2 half_16_19_φ1) (36904696433279/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (201347204957/5000000000000 : ℝ)) half_16_19_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_19_φ1, half_16_19_φ2, half_16_19_φ3, half_16_19_φ4, half_16_19_φ5, half_16_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_19_φ1, half_16_19_φ2, half_16_19_φ3, half_16_19_φ4, half_16_19_φ5, half_16_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_19_φ1, half_16_19_φ2, half_16_19_φ3, half_16_19_φ4, half_16_19_φ5, half_16_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_19 half_16_18
    (by simpa only [half_16_19_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_19_hx2)
  exact h.weaken (by norm_num [half_16_19_φ1, half_16_19_φ2, half_16_19_φ3, half_16_19_φ4, half_16_19_φ5, half_16_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_19 : AdmissibleExponent 18 32 (196497248257901/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 14) (ψ := (206444242957/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_15_19
    (by simpa only [half_16_19_φ1] using half_16_19_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_19_φ1, half_16_19_φ2, half_16_19_φ3, half_16_19_φ4, half_16_19_φ5, half_16_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_17_19_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (421825390801/10000000000000 : ℝ)

def half_17_19_φ2 : Fin 2 → ℝ := Fin.snoc half_17_19_φ1 (5150134853/125000000000 : ℝ)

def half_17_19_φ3 : Fin 3 → ℝ := Fin.snoc half_17_19_φ2 (200561868839/5000000000000 : ℝ)

def half_17_19_φ4 : Fin 4 → ℝ := Fin.snoc half_17_19_φ3 (3096979361/80000000000 : ℝ)

def half_17_19_φ5 : Fin 5 → ℝ := Fin.snoc half_17_19_φ4 (72267928849/2000000000000 : ℝ)

def half_17_19_φ6 : Fin 6 → ℝ := Fin.snoc half_17_19_φ5 (57836676879/2000000000000 : ℝ)

theorem half_17_19_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_17_19_φ6) (21024281590079/2500000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_17_19_φ6 (by norm_num [half_17_19_φ1, half_17_19_φ2, half_17_19_φ3, half_17_19_φ4, half_17_19_φ5, half_17_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_19_φ1, half_17_19_φ2, half_17_19_φ3, half_17_19_φ4, half_17_19_φ5, half_17_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_19_φ1, half_17_19_φ2, half_17_19_φ3, half_17_19_φ4, half_17_19_φ5, half_17_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_17_19_φ1, half_17_19_φ2, half_17_19_φ3, half_17_19_φ4, half_17_19_φ5, half_17_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_17_19_hx6 : SourcePowerBound (powerBoxCross 18 11 64 half_17_19_φ6) (61732014476811/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 11) (r := 2) (v := 14) (w := 15) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_17_19_φ6 (by norm_num [half_17_19_φ1, half_17_19_φ2, half_17_19_φ3, half_17_19_φ4, half_17_19_φ5, half_17_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_19_φ1, half_17_19_φ2, half_17_19_φ3, half_17_19_φ4, half_17_19_φ5, half_17_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_17_19_hF2 half_14_19 half_15_19
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_19_φ1, half_17_19_φ2, half_17_19_φ3, half_17_19_φ4, half_17_19_φ5, half_17_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_19_hx5 : SourcePowerBound (powerBoxCross 18 12 32 half_17_19_φ5) (134165350221239/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 12) (u := 10) (t := 13)
    (D := 32) (ψ := (57836676879/2000000000000 : ℝ)) half_17_19_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_19_φ1, half_17_19_φ2, half_17_19_φ3, half_17_19_φ4, half_17_19_φ5, half_17_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_19_φ1, half_17_19_φ2, half_17_19_φ3, half_17_19_φ4, half_17_19_φ5, half_17_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_19_φ1, half_17_19_φ2, half_17_19_φ3, half_17_19_φ4, half_17_19_φ5, half_17_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_19 half_13_19
    (by simpa only [half_17_19_φ6, show (2:ℝ)*32=64 by norm_num] using half_17_19_hx6)
  exact h.weaken (by norm_num [half_17_19_φ1, half_17_19_φ2, half_17_19_φ3, half_17_19_φ4, half_17_19_φ5, half_17_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_19_hx4 : SourcePowerBound (powerBoxCross 18 13 16 half_17_19_φ4) (147426909766943/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (72267928849/2000000000000 : ℝ)) half_17_19_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_19_φ1, half_17_19_φ2, half_17_19_φ3, half_17_19_φ4, half_17_19_φ5, half_17_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_19_φ1, half_17_19_φ2, half_17_19_φ3, half_17_19_φ4, half_17_19_φ5, half_17_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_19_φ1, half_17_19_φ2, half_17_19_φ3, half_17_19_φ4, half_17_19_φ5, half_17_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_19 half_14_19
    (by simpa only [half_17_19_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_19_hx5)
  exact h.weaken (by norm_num [half_17_19_φ1, half_17_19_φ2, half_17_19_φ3, half_17_19_φ4, half_17_19_φ5, half_17_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_19_hx3 : SourcePowerBound (powerBoxCross 18 14 8 half_17_19_φ3) (162645843293921/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (3096979361/80000000000 : ℝ)) half_17_19_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_19_φ1, half_17_19_φ2, half_17_19_φ3, half_17_19_φ4, half_17_19_φ5, half_17_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_19_φ1, half_17_19_φ2, half_17_19_φ3, half_17_19_φ4, half_17_19_φ5, half_17_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_19_φ1, half_17_19_φ2, half_17_19_φ3, half_17_19_φ4, half_17_19_φ5, half_17_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_19 half_15_19
    (by simpa only [half_17_19_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_19_hx4)
  exact h.weaken (by norm_num [half_17_19_φ1, half_17_19_φ2, half_17_19_φ3, half_17_19_φ4, half_17_19_φ5, half_17_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_19_hx2 : SourcePowerBound (powerBoxCross 18 15 4 half_17_19_φ2) (22463347872343/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (200561868839/5000000000000 : ℝ)) half_17_19_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_19_φ1, half_17_19_φ2, half_17_19_φ3, half_17_19_φ4, half_17_19_φ5, half_17_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_19_φ1, half_17_19_φ2, half_17_19_φ3, half_17_19_φ4, half_17_19_φ5, half_17_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_19_φ1, half_17_19_φ2, half_17_19_φ3, half_17_19_φ4, half_17_19_φ5, half_17_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_19 half_16_19
    (by simpa only [half_17_19_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_19_hx3)
  exact h.weaken (by norm_num [half_17_19_φ1, half_17_19_φ2, half_17_19_φ3, half_17_19_φ4, half_17_19_φ5, half_17_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_19_hx1 : SourcePowerBound (powerBoxCross 18 16 2 half_17_19_φ1) (99315160397471/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (5150134853/125000000000 : ℝ)) half_17_19_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_19_φ1, half_17_19_φ2, half_17_19_φ3, half_17_19_φ4, half_17_19_φ5, half_17_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_19_φ1, half_17_19_φ2, half_17_19_φ3, half_17_19_φ4, half_17_19_φ5, half_17_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_19_φ1, half_17_19_φ2, half_17_19_φ3, half_17_19_φ4, half_17_19_φ5, half_17_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_15_19 half_17_18
    (by simpa only [half_17_19_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_19_hx2)
  exact h.weaken (by norm_num [half_17_19_φ1, half_17_19_φ2, half_17_19_φ3, half_17_19_φ4, half_17_19_φ5, half_17_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_19 : AdmissibleExponent 18 34 (211706907909773/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 15) (ψ := (421825390801/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_16_19
    (by simpa only [half_17_19_φ1] using half_17_19_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_19_φ1, half_17_19_φ2, half_17_19_φ3, half_17_19_φ4, half_17_19_φ5, half_17_19_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])


end Waring.SeedCompletionHigher18SimpleSeeds
