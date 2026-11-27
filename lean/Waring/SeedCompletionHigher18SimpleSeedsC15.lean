import Waring.SeedCompletionHigher18SimpleSeedsC14

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionHigher18SimpleSeeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges

def half_9_15_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (42979853809/1250000000000 : ℝ)

def half_9_15_φ2 : Fin 2 → ℝ := Fin.snoc half_9_15_φ1 (77086285859/2500000000000 : ℝ)

def half_9_15_φ3 : Fin 3 → ℝ := Fin.snoc half_9_15_φ2 (67222954543/5000000000000 : ℝ)

theorem half_9_15_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_9_15_φ3) (34940937983653/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_15_φ3 (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_15_hF1 : SourcePowerBound (paddedMoment 18 0 1 8 half_9_15_φ3) (13313645994551/5000000000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_15_φ3 (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_15_hx3 : SourcePowerBound (powerBoxCross 18 6 8 half_9_15_φ3) (76993037094947/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 6) (r := 1) (v := 2) (t := 10) (D := 8)
    (a := (3/10 : ℝ)) (b := (1/10 : ℝ)) (c := (3/5 : ℝ))
    (by norm_num) half_9_15_φ3 (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_15_hF1 half_9_15_hF2 half_10_14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_15_hx2 : SourcePowerBound (powerBoxCross 18 7 4 half_9_15_φ2) (84269421792529/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (67222954543/5000000000000 : ℝ)) half_9_15_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_6 SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_15_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_15_hx3)
  exact h.weaken (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_15_hx1 : SourcePowerBound (powerBoxCross 18 8 2 half_9_15_φ1) (18834959609051/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (77086285859/2500000000000 : ℝ)) half_9_15_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_14
    (by simpa only [half_9_15_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_15_hx2)
  exact h.weaken (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_15 : AdmissibleExponent 18 18 (19866476100467/2000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 7) (ψ := (42979853809/1250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_15_φ1] using half_9_15_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_15_φ1, half_9_15_φ2, half_9_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_10_15_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (353748846267/10000000000000 : ℝ)

def half_10_15_φ2 : Fin 2 → ℝ := Fin.snoc half_10_15_φ1 (164628283337/5000000000000 : ℝ)

def half_10_15_φ3 : Fin 3 → ℝ := Fin.snoc half_10_15_φ2 (229938781391/10000000000000 : ℝ)

theorem half_10_15_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_10_15_φ3) (15859961522267/2500000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_15_φ3 (by norm_num [half_10_15_φ1, half_10_15_φ2, half_10_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_15_φ1, half_10_15_φ2, half_10_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_15_φ1, half_10_15_φ2, half_10_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_10_15_φ1, half_10_15_φ2, half_10_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_10_15_hx3 : SourcePowerBound (powerBoxCross 18 7 8 half_10_15_φ3) (86477914165091/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 7) (r := 2) (v := 9) (w := 10) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_10_15_φ3 (by norm_num [half_10_15_φ1, half_10_15_φ2, half_10_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_15_φ1, half_10_15_φ2, half_10_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_15_hF2 half_9_15 half_10_14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_15_φ1, half_10_15_φ2, half_10_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_15_hx2 : SourcePowerBound (powerBoxCross 18 8 4 half_10_15_φ2) (47600987862293/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (229938781391/10000000000000 : ℝ)) half_10_15_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_15_φ1, half_10_15_φ2, half_10_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_15_φ1, half_10_15_φ2, half_10_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_15_φ1, half_10_15_φ2, half_10_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_15
    (by simpa only [half_10_15_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_15_hx3)
  exact h.weaken (by norm_num [half_10_15_φ1, half_10_15_φ2, half_10_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_15_hx1 : SourcePowerBound (powerBoxCross 18 9 2 half_10_15_φ1) (2123445156973/200000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (164628283337/5000000000000 : ℝ)) half_10_15_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_15_φ1, half_10_15_φ2, half_10_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_15_φ1, half_10_15_φ2, half_10_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_15_φ1, half_10_15_φ2, half_10_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_14
    (by simpa only [half_10_15_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_15_hx2)
  exact h.weaken (by norm_num [half_10_15_φ1, half_10_15_φ2, half_10_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_15 : AdmissibleExponent 18 20 (112185988235189/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 8) (ψ := (353748846267/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_9_15
    (by simpa only [half_10_15_φ1] using half_10_15_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_15_φ1, half_10_15_φ2, half_10_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_11_15_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (91187034513/2500000000000 : ℝ)

def half_11_15_φ2 : Fin 2 → ℝ := Fin.snoc half_11_15_φ1 (173197429361/5000000000000 : ℝ)

def half_11_15_φ3 : Fin 3 → ℝ := Fin.snoc half_11_15_φ2 (294728498171/10000000000000 : ℝ)

theorem half_11_15_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_11_15_φ3) (11740110751561/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_15_φ3 (by norm_num [half_11_15_φ1, half_11_15_φ2, half_11_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_15_φ1, half_11_15_φ2, half_11_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_15_φ1, half_11_15_φ2, half_11_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_15_φ1, half_11_15_φ2, half_11_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_11_15_hx3 : SourcePowerBound (powerBoxCross 18 8 8 half_11_15_φ3) (9628875190329/1000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 8) (r := 2) (v := 10) (w := 11) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_11_15_φ3 (by norm_num [half_11_15_φ1, half_11_15_φ2, half_11_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_15_φ1, half_11_15_φ2, half_11_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_15_hF2 half_10_15 half_11_14
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_15_φ1, half_11_15_φ2, half_11_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_15_hx2 : SourcePowerBound (powerBoxCross 18 9 4 half_11_15_φ2) (53207052169731/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (294728498171/10000000000000 : ℝ)) half_11_15_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_15_φ1, half_11_15_φ2, half_11_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_15_φ1, half_11_15_φ2, half_11_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_15_φ1, half_11_15_φ2, half_11_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_15
    (by simpa only [half_11_15_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_15_hx3)
  exact h.weaken (by norm_num [half_11_15_φ1, half_11_15_φ2, half_11_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_15_hx1 : SourcePowerBound (powerBoxCross 18 10 2 half_11_15_φ1) (59229386670411/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (173197429361/5000000000000 : ℝ)) half_11_15_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_15_φ1, half_11_15_φ2, half_11_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_15_φ1, half_11_15_φ2, half_11_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_15_φ1, half_11_15_φ2, half_11_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_15 half_11_14
    (by simpa only [half_11_15_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_15_hx2)
  exact h.weaken (by norm_num [half_11_15_φ1, half_11_15_φ2, half_11_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_15 : AdmissibleExponent 18 22 (12538898796381/1000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 9) (ψ := (91187034513/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_10_15
    (by simpa only [half_11_15_φ1] using half_11_15_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_15_φ1, half_11_15_φ2, half_11_15_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_12_15_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (187470986421/5000000000000 : ℝ)

def half_12_15_φ2 : Fin 2 → ℝ := Fin.snoc half_12_15_φ1 (180293432947/5000000000000 : ℝ)

def half_12_15_φ3 : Fin 3 → ℝ := Fin.snoc half_12_15_φ2 (329430071429/10000000000000 : ℝ)

def half_12_15_φ4 : Fin 4 → ℝ := Fin.snoc half_12_15_φ3 (53226838893/2500000000000 : ℝ)

theorem half_12_15_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_12_15_φ4) (74828820447413/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_15_φ4 (by norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_15_hF1 : SourcePowerBound (paddedMoment 18 0 1 16 half_12_15_φ4) (28276273482471/10000000000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_15_φ4 (by norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_15_hx4 : SourcePowerBound (powerBoxCross 18 8 16 half_12_15_φ4) (9783070957447/1000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 8) (r := 1) (v := 2) (t := 11) (D := 16)
    (a := (1/22 : ℝ)) (b := (5/22 : ℝ)) (c := (8/11 : ℝ))
    (by norm_num) half_12_15_φ4 (by norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_15_hF1 half_12_15_hF2 half_11_15
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_15_hx3 : SourcePowerBound (powerBoxCross 18 9 8 half_12_15_φ3) (106579329946881/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (53226838893/2500000000000 : ℝ)) half_12_15_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_15
    (by simpa only [half_12_15_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_15_hx4)
  exact h.weaken (by norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_15_hx2 : SourcePowerBound (powerBoxCross 18 10 4 half_12_15_φ2) (117920958597871/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (329430071429/10000000000000 : ℝ)) half_12_15_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_15 half_11_15
    (by simpa only [half_12_15_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_15_hx3)
  exact h.weaken (by norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_15_hx1 : SourcePowerBound (powerBoxCross 18 11 2 half_12_15_φ1) (65531285242339/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (180293432947/5000000000000 : ℝ)) half_12_15_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_15 half_12_14
    (by simpa only [half_12_15_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_15_hx2)
  exact h.weaken (by norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_15 : AdmissibleExponent 18 24 (3473408797859/250000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 10) (ψ := (187470986421/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_11_15
    (by simpa only [half_12_15_φ1] using half_12_15_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_15_φ1, half_12_15_φ2, half_12_15_φ3, half_12_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_13_15_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (384604490489/10000000000000 : ℝ)

def half_13_15_φ2 : Fin 2 → ℝ := Fin.snoc half_13_15_φ1 (185984205533/5000000000000 : ℝ)

def half_13_15_φ3 : Fin 3 → ℝ := Fin.snoc half_13_15_φ2 (34989316381/1000000000000 : ℝ)

def half_13_15_φ4 : Fin 4 → ℝ := Fin.snoc half_13_15_φ3 (14165664949/500000000000 : ℝ)

theorem half_13_15_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_13_15_φ4) (13824250483681/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_15_φ4 (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_13_15_hx4 : SourcePowerBound (powerBoxCross 18 9 16 half_13_15_φ4) (4280030457071/400000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 16)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_13_15_φ4 (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_15_hF2 half_12_15 half_12_15
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_15_hx3 : SourcePowerBound (powerBoxCross 18 10 8 half_13_15_φ3) (586305715867/50000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (14165664949/500000000000 : ℝ)) half_13_15_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_15 half_11_15
    (by simpa only [half_13_15_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_15_hx4)
  exact h.weaken (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_15_hx2 : SourcePowerBound (powerBoxCross 18 11 4 half_13_15_φ2) (32434022247973/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (34989316381/1000000000000 : ℝ)) half_13_15_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_15 half_12_15
    (by simpa only [half_13_15_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_15_hx3)
  exact h.weaken (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_15_hx1 : SourcePowerBound (powerBoxCross 18 12 2 half_13_15_φ1) (143977401921021/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (185984205533/5000000000000 : ℝ)) half_13_15_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_15 half_13_14
    (by simpa only [half_13_15_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_15_hx2)
  exact h.weaken (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_15 : AdmissibleExponent 18 26 (38205826300567/2500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 11) (ψ := (384604490489/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_12_15
    (by simpa only [half_13_15_φ1] using half_13_15_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_15_φ1, half_13_15_φ2, half_13_15_φ3, half_13_15_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_14_15_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (197180486179/5000000000000 : ℝ)

def half_14_15_φ2 : Fin 2 → ℝ := Fin.snoc half_14_15_φ1 (191498373163/5000000000000 : ℝ)

def half_14_15_φ3 : Fin 3 → ℝ := Fin.snoc half_14_15_φ2 (73452163651/2000000000000 : ℝ)

def half_14_15_φ4 : Fin 4 → ℝ := Fin.snoc half_14_15_φ3 (20757235547/625000000000 : ℝ)

def half_14_15_φ5 : Fin 5 → ℝ := Fin.snoc half_14_15_φ4 (41116165427/2000000000000 : ℝ)

theorem half_14_15_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_14_15_φ5) (42100964112937/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_14_15_φ5 (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_14_15_hx5 : SourcePowerBound (powerBoxCross 18 9 32 half_14_15_φ5) (26930660360713/2500000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_14_15_φ5 (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_15_hF2 half_12_15 half_12_15
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_15_hx4 : SourcePowerBound (powerBoxCross 18 10 16 half_14_15_φ4) (7280793695719/625000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (41116165427/2000000000000 : ℝ)) half_14_15_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_15 half_11_15
    (by simpa only [half_14_15_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_15_hx5)
  exact h.weaken (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_15_hx3 : SourcePowerBound (powerBoxCross 18 11 8 half_14_15_φ3) (64094455784651/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (20757235547/625000000000 : ℝ)) half_14_15_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_15 half_12_15
    (by simpa only [half_14_15_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_15_hx4)
  exact h.weaken (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_15_hx2 : SourcePowerBound (powerBoxCross 18 12 4 half_14_15_φ2) (3545372189349/250000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (73452163651/2000000000000 : ℝ)) half_14_15_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_15 half_13_15
    (by simpa only [half_14_15_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_15_hx3)
  exact h.weaken (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_15_hx1 : SourcePowerBound (powerBoxCross 18 13 2 half_14_15_φ1) (19648863931349/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (191498373163/5000000000000 : ℝ)) half_14_15_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_15 half_14_14
    (by simpa only [half_14_15_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_15_hx2)
  exact h.weaken (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_15 : AdmissibleExponent 18 28 (83524967879871/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 12) (ψ := (197180486179/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_13_15
    (by simpa only [half_14_15_φ1] using half_14_15_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_15_φ1, half_14_15_φ2, half_14_15_φ3, half_14_15_φ4, half_14_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_15_15_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (201819285091/5000000000000 : ℝ)

def half_15_15_φ2 : Fin 2 → ℝ := Fin.snoc half_15_15_φ1 (196493807941/5000000000000 : ℝ)

def half_15_15_φ3 : Fin 3 → ℝ := Fin.snoc half_15_15_φ2 (189728777637/5000000000000 : ℝ)

def half_15_15_φ4 : Fin 4 → ℝ := Fin.snoc half_15_15_φ3 (35522516143/1000000000000 : ℝ)

def half_15_15_φ5 : Fin 5 → ℝ := Fin.snoc half_15_15_φ4 (11371644863/400000000000 : ℝ)

theorem half_15_15_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_15_15_φ5) (77404398758507/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_15_15_φ5 (by norm_num [half_15_15_φ1, half_15_15_φ2, half_15_15_φ3, half_15_15_φ4, half_15_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_15_φ1, half_15_15_φ2, half_15_15_φ3, half_15_15_φ4, half_15_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_15_φ1, half_15_15_φ2, half_15_15_φ3, half_15_15_φ4, half_15_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_15_15_φ1, half_15_15_φ2, half_15_15_φ3, half_15_15_φ4, half_15_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_15_15_hx5 : SourcePowerBound (powerBoxCross 18 10 32 half_15_15_φ5) (116069539712629/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_15_15_φ5 (by norm_num [half_15_15_φ1, half_15_15_φ2, half_15_15_φ3, half_15_15_φ4, half_15_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_15_φ1, half_15_15_φ2, half_15_15_φ3, half_15_15_φ4, half_15_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_15_15_hF2 half_13_15 half_14_15
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_15_φ1, half_15_15_φ2, half_15_15_φ3, half_15_15_φ4, half_15_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_15_hx4 : SourcePowerBound (powerBoxCross 18 11 16 half_15_15_φ4) (126549862164703/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (11371644863/400000000000 : ℝ)) half_15_15_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_15_φ1, half_15_15_φ2, half_15_15_φ3, half_15_15_φ4, half_15_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_15_φ1, half_15_15_φ2, half_15_15_φ3, half_15_15_φ4, half_15_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_15_φ1, half_15_15_φ2, half_15_15_φ3, half_15_15_φ4, half_15_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_15 half_12_15
    (by simpa only [half_15_15_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_15_hx5)
  exact h.weaken (by norm_num [half_15_15_φ1, half_15_15_φ2, half_15_15_φ3, half_15_15_φ4, half_15_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_15_hx3 : SourcePowerBound (powerBoxCross 18 12 8 half_15_15_φ3) (17429135731229/1250000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (35522516143/1000000000000 : ℝ)) half_15_15_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_15_φ1, half_15_15_φ2, half_15_15_φ3, half_15_15_φ4, half_15_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_15_φ1, half_15_15_φ2, half_15_15_φ3, half_15_15_φ4, half_15_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_15_φ1, half_15_15_φ2, half_15_15_φ3, half_15_15_φ4, half_15_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_15 half_13_15
    (by simpa only [half_15_15_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_15_hx4)
  exact h.weaken (by norm_num [half_15_15_φ1, half_15_15_φ2, half_15_15_φ3, half_15_15_φ4, half_15_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_15_hx2 : SourcePowerBound (powerBoxCross 18 13 4 half_15_15_φ2) (154180132448569/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (189728777637/5000000000000 : ℝ)) half_15_15_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_15_φ1, half_15_15_φ2, half_15_15_φ3, half_15_15_φ4, half_15_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_15_φ1, half_15_15_φ2, half_15_15_φ3, half_15_15_φ4, half_15_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_15_φ1, half_15_15_φ2, half_15_15_φ3, half_15_15_φ4, half_15_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_15 half_14_15
    (by simpa only [half_15_15_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_15_hx3)
  exact h.weaken (by norm_num [half_15_15_φ1, half_15_15_φ2, half_15_15_φ3, half_15_15_φ4, half_15_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_15_hx1 : SourcePowerBound (powerBoxCross 18 14 2 half_15_15_φ1) (85355397304019/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (196493807941/5000000000000 : ℝ)) half_15_15_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_15_φ1, half_15_15_φ2, half_15_15_φ3, half_15_15_φ4, half_15_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_15_φ1, half_15_15_φ2, half_15_15_φ3, half_15_15_φ4, half_15_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_15_φ1, half_15_15_φ2, half_15_15_φ3, half_15_15_φ4, half_15_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_15 half_15_14
    (by simpa only [half_15_15_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_15_hx2)
  exact h.weaken (by norm_num [half_15_15_φ1, half_15_15_φ2, half_15_15_φ3, half_15_15_φ4, half_15_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_15 : AdmissibleExponent 18 30 (22701129500369/1250000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 13) (ψ := (201819285091/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_14_15
    (by simpa only [half_15_15_φ1] using half_15_15_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_15_φ1, half_15_15_φ2, half_15_15_φ3, half_15_15_φ4, half_15_15_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_16_15_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (412891186027/10000000000000 : ℝ)

def half_16_15_φ2 : Fin 2 → ℝ := Fin.snoc half_16_15_φ1 (16107784863/400000000000 : ℝ)

def half_16_15_φ3 : Fin 3 → ℝ := Fin.snoc half_16_15_φ2 (97774344847/2500000000000 : ℝ)

def half_16_15_φ4 : Fin 4 → ℝ := Fin.snoc half_16_15_φ3 (374102532913/10000000000000 : ℝ)

def half_16_15_φ5 : Fin 5 → ℝ := Fin.snoc half_16_15_φ4 (336301618233/10000000000000 : ℝ)

def half_16_15_φ6 : Fin 6 → ℝ := Fin.snoc half_16_15_φ5 (208225501453/10000000000000 : ℝ)

theorem half_16_15_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_16_15_φ6) (91609045180961/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_16_15_φ6 (by norm_num [half_16_15_φ1, half_16_15_φ2, half_16_15_φ3, half_16_15_φ4, half_16_15_φ5, half_16_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_15_φ1, half_16_15_φ2, half_16_15_φ3, half_16_15_φ4, half_16_15_φ5, half_16_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_15_φ1, half_16_15_φ2, half_16_15_φ3, half_16_15_φ4, half_16_15_φ5, half_16_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_16_15_φ1, half_16_15_φ2, half_16_15_φ3, half_16_15_φ4, half_16_15_φ5, half_16_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_16_15_hx6 : SourcePowerBound (powerBoxCross 18 10 64 half_16_15_φ6) (57980348433251/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_16_15_φ6 (by norm_num [half_16_15_φ1, half_16_15_φ2, half_16_15_φ3, half_16_15_φ4, half_16_15_φ5, half_16_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_15_φ1, half_16_15_φ2, half_16_15_φ3, half_16_15_φ4, half_16_15_φ5, half_16_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_16_15_hF2 half_13_15 half_14_15
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_15_φ1, half_16_15_φ2, half_16_15_φ3, half_16_15_φ4, half_16_15_φ5, half_16_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_15_hx5 : SourcePowerBound (powerBoxCross 18 11 32 half_16_15_φ5) (12481376822699/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 11) (u := 9) (t := 12)
    (D := 32) (ψ := (208225501453/10000000000000 : ℝ)) half_16_15_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_15_φ1, half_16_15_φ2, half_16_15_φ3, half_16_15_φ4, half_16_15_φ5, half_16_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_15_φ1, half_16_15_φ2, half_16_15_φ3, half_16_15_φ4, half_16_15_φ5, half_16_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_15_φ1, half_16_15_φ2, half_16_15_φ3, half_16_15_φ4, half_16_15_φ5, half_16_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_15 half_12_15
    (by simpa only [half_16_15_φ6, show (2:ℝ)*32=64 by norm_num] using half_16_15_hx6)
  exact h.weaken (by norm_num [half_16_15_φ1, half_16_15_φ2, half_16_15_φ3, half_16_15_φ4, half_16_15_φ5, half_16_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_15_hx4 : SourcePowerBound (powerBoxCross 18 12 16 half_16_15_φ4) (68416990080147/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (336301618233/10000000000000 : ℝ)) half_16_15_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_15_φ1, half_16_15_φ2, half_16_15_φ3, half_16_15_φ4, half_16_15_φ5, half_16_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_15_φ1, half_16_15_φ2, half_16_15_φ3, half_16_15_φ4, half_16_15_φ5, half_16_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_15_φ1, half_16_15_φ2, half_16_15_φ3, half_16_15_φ4, half_16_15_φ5, half_16_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_15 half_13_15
    (by simpa only [half_16_15_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_15_hx5)
  exact h.weaken (by norm_num [half_16_15_φ1, half_16_15_φ2, half_16_15_φ3, half_16_15_φ4, half_16_15_φ5, half_16_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_15_hx3 : SourcePowerBound (powerBoxCross 18 13 8 half_16_15_φ3) (150908512555651/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (374102532913/10000000000000 : ℝ)) half_16_15_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_15_φ1, half_16_15_φ2, half_16_15_φ3, half_16_15_φ4, half_16_15_φ5, half_16_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_15_φ1, half_16_15_φ2, half_16_15_φ3, half_16_15_φ4, half_16_15_φ5, half_16_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_15_φ1, half_16_15_φ2, half_16_15_φ3, half_16_15_φ4, half_16_15_φ5, half_16_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_15 half_14_15
    (by simpa only [half_16_15_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_15_hx4)
  exact h.weaken (by norm_num [half_16_15_φ1, half_16_15_φ2, half_16_15_φ3, half_16_15_φ4, half_16_15_φ5, half_16_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_15_hx2 : SourcePowerBound (powerBoxCross 18 14 4 half_16_15_φ2) (166809124542221/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (97774344847/2500000000000 : ℝ)) half_16_15_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_15_φ1, half_16_15_φ2, half_16_15_φ3, half_16_15_φ4, half_16_15_φ5, half_16_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_15_φ1, half_16_15_φ2, half_16_15_φ3, half_16_15_φ4, half_16_15_φ5, half_16_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_15_φ1, half_16_15_φ2, half_16_15_φ3, half_16_15_φ4, half_16_15_φ5, half_16_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_15 half_15_15
    (by simpa only [half_16_15_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_15_hx3)
  exact h.weaken (by norm_num [half_16_15_φ1, half_16_15_φ2, half_16_15_φ3, half_16_15_φ4, half_16_15_φ5, half_16_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_15_hx1 : SourcePowerBound (powerBoxCross 18 15 2 half_16_15_φ1) (184523450162149/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (16107784863/400000000000 : ℝ)) half_16_15_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_15_φ1, half_16_15_φ2, half_16_15_φ3, half_16_15_φ4, half_16_15_φ5, half_16_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_15_φ1, half_16_15_φ2, half_16_15_φ3, half_16_15_φ4, half_16_15_φ5, half_16_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_15_φ1, half_16_15_φ2, half_16_15_φ3, half_16_15_φ4, half_16_15_φ5, half_16_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_15 half_16_14
    (by simpa only [half_16_15_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_15_hx2)
  exact h.weaken (by norm_num [half_16_15_φ1, half_16_15_φ2, half_16_15_φ3, half_16_15_φ4, half_16_15_φ5, half_16_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_15 : AdmissibleExponent 18 32 (49124323639233/2500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 14) (ψ := (412891186027/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_15_15
    (by simpa only [half_16_15_φ1] using half_16_15_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_15_φ1, half_16_15_φ2, half_16_15_φ3, half_16_15_φ4, half_16_15_φ5, half_16_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_17_15_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (105458031651/2500000000000 : ℝ)

def half_17_15_φ2 : Fin 2 → ℝ := Fin.snoc half_17_15_φ1 (206005689381/5000000000000 : ℝ)

def half_17_15_φ3 : Fin 3 → ℝ := Fin.snoc half_17_15_φ2 (200561992023/5000000000000 : ℝ)

def half_17_15_φ4 : Fin 4 → ℝ := Fin.snoc half_17_15_φ3 (387122655077/10000000000000 : ℝ)

def half_17_15_φ5 : Fin 5 → ℝ := Fin.snoc half_17_15_φ4 (90335078377/2500000000000 : ℝ)

def half_17_15_φ6 : Fin 6 → ℝ := Fin.snoc half_17_15_φ5 (72296476741/2500000000000 : ℝ)

theorem half_17_15_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_17_15_φ6) (84096565386989/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_17_15_φ6 (by norm_num [half_17_15_φ1, half_17_15_φ2, half_17_15_φ3, half_17_15_φ4, half_17_15_φ5, half_17_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_15_φ1, half_17_15_φ2, half_17_15_φ3, half_17_15_φ4, half_17_15_φ5, half_17_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_15_φ1, half_17_15_φ2, half_17_15_φ3, half_17_15_φ4, half_17_15_φ5, half_17_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_17_15_φ1, half_17_15_φ2, half_17_15_φ3, half_17_15_φ4, half_17_15_φ5, half_17_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_17_15_hx6 : SourcePowerBound (powerBoxCross 18 11 64 half_17_15_φ6) (30865937370393/2500000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 11) (r := 2) (v := 14) (w := 15) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_17_15_φ6 (by norm_num [half_17_15_φ1, half_17_15_φ2, half_17_15_φ3, half_17_15_φ4, half_17_15_φ5, half_17_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_15_φ1, half_17_15_φ2, half_17_15_φ3, half_17_15_φ4, half_17_15_φ5, half_17_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_17_15_hF2 half_14_15 half_15_15
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_15_φ1, half_17_15_φ2, half_17_15_φ3, half_17_15_φ4, half_17_15_φ5, half_17_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_15_hx5 : SourcePowerBound (powerBoxCross 18 12 32 half_17_15_φ5) (67082550280287/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 12) (u := 10) (t := 13)
    (D := 32) (ψ := (72296476741/2500000000000 : ℝ)) half_17_15_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_15_φ1, half_17_15_φ2, half_17_15_φ3, half_17_15_φ4, half_17_15_φ5, half_17_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_15_φ1, half_17_15_φ2, half_17_15_φ3, half_17_15_φ4, half_17_15_φ5, half_17_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_15_φ1, half_17_15_φ2, half_17_15_φ3, half_17_15_φ4, half_17_15_φ5, half_17_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_15 half_13_15
    (by simpa only [half_17_15_φ6, show (2:ℝ)*32=64 by norm_num] using half_17_15_hx6)
  exact h.weaken (by norm_num [half_17_15_φ1, half_17_15_φ2, half_17_15_φ3, half_17_15_φ4, half_17_15_φ5, half_17_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_15_hx4 : SourcePowerBound (powerBoxCross 18 13 16 half_17_15_φ4) (73713331407837/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (90335078377/2500000000000 : ℝ)) half_17_15_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_15_φ1, half_17_15_φ2, half_17_15_φ3, half_17_15_φ4, half_17_15_φ5, half_17_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_15_φ1, half_17_15_φ2, half_17_15_φ3, half_17_15_φ4, half_17_15_φ5, half_17_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_15_φ1, half_17_15_φ2, half_17_15_φ3, half_17_15_φ4, half_17_15_φ5, half_17_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_15 half_14_15
    (by simpa only [half_17_15_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_15_hx5)
  exact h.weaken (by norm_num [half_17_15_φ1, half_17_15_φ2, half_17_15_φ3, half_17_15_φ4, half_17_15_φ5, half_17_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_15_hx3 : SourcePowerBound (powerBoxCross 18 14 8 half_17_15_φ3) (162645596175419/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (387122655077/10000000000000 : ℝ)) half_17_15_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_15_φ1, half_17_15_φ2, half_17_15_φ3, half_17_15_φ4, half_17_15_φ5, half_17_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_15_φ1, half_17_15_φ2, half_17_15_φ3, half_17_15_φ4, half_17_15_φ5, half_17_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_15_φ1, half_17_15_φ2, half_17_15_φ3, half_17_15_φ4, half_17_15_φ5, half_17_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_15 half_15_15
    (by simpa only [half_17_15_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_15_hx4)
  exact h.weaken (by norm_num [half_17_15_φ1, half_17_15_φ2, half_17_15_φ3, half_17_15_φ4, half_17_15_φ5, half_17_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_15_hx2 : SourcePowerBound (powerBoxCross 18 15 4 half_17_15_φ2) (44926637427693/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (200561992023/5000000000000 : ℝ)) half_17_15_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_15_φ1, half_17_15_φ2, half_17_15_φ3, half_17_15_φ4, half_17_15_φ5, half_17_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_15_φ1, half_17_15_φ2, half_17_15_φ3, half_17_15_φ4, half_17_15_φ5, half_17_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_15_φ1, half_17_15_φ2, half_17_15_φ3, half_17_15_φ4, half_17_15_φ5, half_17_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_15 half_16_15
    (by simpa only [half_17_15_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_15_hx3)
  exact h.weaken (by norm_num [half_17_15_φ1, half_17_15_φ2, half_17_15_φ3, half_17_15_φ4, half_17_15_φ5, half_17_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_15_hx1 : SourcePowerBound (powerBoxCross 18 16 2 half_17_15_φ1) (198630239520069/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (206005689381/5000000000000 : ℝ)) half_17_15_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_15_φ1, half_17_15_φ2, half_17_15_φ3, half_17_15_φ4, half_17_15_φ5, half_17_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_15_φ1, half_17_15_φ2, half_17_15_φ3, half_17_15_φ4, half_17_15_φ5, half_17_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_15_φ1, half_17_15_φ2, half_17_15_φ3, half_17_15_φ4, half_17_15_φ5, half_17_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_15_15 half_17_14
    (by simpa only [half_17_15_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_15_hx2)
  exact h.weaken (by norm_num [half_17_15_φ1, half_17_15_φ2, half_17_15_φ3, half_17_15_φ4, half_17_15_φ5, half_17_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_15 : AdmissibleExponent 18 34 (211707035444793/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 15) (ψ := (105458031651/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_16_15
    (by simpa only [half_17_15_φ1] using half_17_15_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_15_φ1, half_17_15_φ2, half_17_15_φ3, half_17_15_φ4, half_17_15_φ5, half_17_15_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])


end Waring.SeedCompletionHigher18SimpleSeeds
