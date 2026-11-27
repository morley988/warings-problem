import Waring.SeedCompletionHigher18SimpleSeedsC16

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionHigher18SimpleSeeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges

def half_9_17_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (343838830337/10000000000000 : ℝ)

def half_9_17_φ2 : Fin 2 → ℝ := Fin.snoc half_9_17_φ1 (77086285817/2500000000000 : ℝ)

def half_9_17_φ3 : Fin 3 → ℝ := Fin.snoc half_9_17_φ2 (67222954013/5000000000000 : ℝ)

theorem half_9_17_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_9_17_φ3) (69881876036819/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_17_φ3 (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_17_hF1 : SourcePowerBound (paddedMoment 18 0 1 8 half_9_17_φ3) (26627292012273/10000000000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_17_φ3 (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_17_hx3 : SourcePowerBound (powerBoxCross 18 6 8 half_9_17_φ3) (15398607421521/2000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 6) (r := 1) (v := 2) (t := 10) (D := 8)
    (a := (3/10 : ℝ)) (b := (1/10 : ℝ)) (c := (3/5 : ℝ))
    (by norm_num) half_9_17_φ3 (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_17_hF1 half_9_17_hF2 half_10_16
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_17_hx2 : SourcePowerBound (powerBoxCross 18 7 4 half_9_17_φ2) (84269421796919/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (67222954013/5000000000000 : ℝ)) half_9_17_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_6 SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_17_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_17_hx3)
  exact h.weaken (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_17_hx1 : SourcePowerBound (powerBoxCross 18 8 2 half_9_17_φ1) (2942962438947/312500000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (77086285817/2500000000000 : ℝ)) half_9_17_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_16
    (by simpa only [half_9_17_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_17_hx2)
  exact h.weaken (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_17 : AdmissibleExponent 18 18 (99332380501359/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 7) (ψ := (343838830337/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_17_φ1] using half_9_17_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_17_φ1, half_9_17_φ2, half_9_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_10_17_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (353748845791/10000000000000 : ℝ)

def half_10_17_φ2 : Fin 2 → ℝ := Fin.snoc half_10_17_φ1 (164628283279/5000000000000 : ℝ)

def half_10_17_φ3 : Fin 3 → ℝ := Fin.snoc half_10_17_φ2 (229938780889/10000000000000 : ℝ)

theorem half_10_17_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_10_17_φ3) (31719923072431/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_17_φ3 (by norm_num [half_10_17_φ1, half_10_17_φ2, half_10_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_17_φ1, half_10_17_φ2, half_10_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_17_φ1, half_10_17_φ2, half_10_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_10_17_φ1, half_10_17_φ2, half_10_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_10_17_hx3 : SourcePowerBound (powerBoxCross 18 7 8 half_10_17_φ3) (2702434818213/312500000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 7) (r := 2) (v := 9) (w := 10) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_10_17_φ3 (by norm_num [half_10_17_φ1, half_10_17_φ2, half_10_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_17_φ1, half_10_17_φ2, half_10_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_17_hF2 half_9_17 half_10_16
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_17_φ1, half_10_17_φ2, half_10_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_17_hx2 : SourcePowerBound (powerBoxCross 18 8 4 half_10_17_φ2) (47600987868853/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (229938780889/10000000000000 : ℝ)) half_10_17_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_17_φ1, half_10_17_φ2, half_10_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_17_φ1, half_10_17_φ2, half_10_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_17_φ1, half_10_17_φ2, half_10_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_17
    (by simpa only [half_10_17_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_17_hx3)
  exact h.weaken (by norm_num [half_10_17_φ1, half_10_17_φ2, half_10_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_17_hx1 : SourcePowerBound (powerBoxCross 18 9 2 half_10_17_φ1) (21234451570393/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (164628283279/5000000000000 : ℝ)) half_10_17_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_17_φ1, half_10_17_φ2, half_10_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_17_φ1, half_10_17_φ2, half_10_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_17_φ1, half_10_17_φ2, half_10_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_16
    (by simpa only [half_10_17_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_17_hx2)
  exact h.weaken (by norm_num [half_10_17_φ1, half_10_17_φ2, half_10_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_17 : AdmissibleExponent 18 20 (28046497057603/2500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 8) (ψ := (353748845791/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_9_17
    (by simpa only [half_10_17_φ1] using half_10_17_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_17_φ1, half_10_17_φ2, half_10_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_11_17_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (9118703347/250000000000 : ℝ)

def half_11_17_φ2 : Fin 2 → ℝ := Fin.snoc half_11_17_φ1 (346394857341/10000000000000 : ℝ)

def half_11_17_φ3 : Fin 3 → ℝ := Fin.snoc half_11_17_φ2 (294728491713/10000000000000 : ℝ)

theorem half_11_17_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_11_17_φ3) (29350277185183/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_17_φ3 (by norm_num [half_11_17_φ1, half_11_17_φ2, half_11_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_17_φ1, half_11_17_φ2, half_11_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_17_φ1, half_11_17_φ2, half_11_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_17_φ1, half_11_17_φ2, half_11_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_11_17_hx3 : SourcePowerBound (powerBoxCross 18 8 8 half_11_17_φ3) (192577504191/20000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 8) (r := 2) (v := 10) (w := 11) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_11_17_φ3 (by norm_num [half_11_17_φ1, half_11_17_φ2, half_11_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_17_φ1, half_11_17_φ2, half_11_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_17_hF2 half_10_17 half_11_16
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_17_φ1, half_11_17_φ2, half_11_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_17_hx2 : SourcePowerBound (powerBoxCross 18 9 4 half_11_17_φ2) (106414104463263/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (294728491713/10000000000000 : ℝ)) half_11_17_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_17_φ1, half_11_17_φ2, half_11_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_17_φ1, half_11_17_φ2, half_11_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_17_φ1, half_11_17_φ2, half_11_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_17
    (by simpa only [half_11_17_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_17_hx3)
  exact h.weaken (by norm_num [half_11_17_φ1, half_11_17_φ2, half_11_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_17_hx1 : SourcePowerBound (powerBoxCross 18 10 2 half_11_17_φ1) (118458773378849/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (346394857341/10000000000000 : ℝ)) half_11_17_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_17_φ1, half_11_17_φ2, half_11_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_17_φ1, half_11_17_φ2, half_11_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_17_φ1, half_11_17_φ2, half_11_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_17 half_11_16
    (by simpa only [half_11_17_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_17_hx2)
  exact h.weaken (by norm_num [half_11_17_φ1, half_11_17_φ2, half_11_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_17 : AdmissibleExponent 18 22 (125388987922569/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 9) (ψ := (9118703347/250000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_10_17
    (by simpa only [half_11_17_φ1] using half_11_17_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_17_φ1, half_11_17_φ2, half_11_17_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_12_17_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (374941955653/10000000000000 : ℝ)

def half_12_17_φ2 : Fin 2 → ℝ := Fin.snoc half_12_17_φ1 (45073358087/1250000000000 : ℝ)

def half_12_17_φ3 : Fin 3 → ℝ := Fin.snoc half_12_17_φ2 (41178758719/1250000000000 : ℝ)

def half_12_17_φ4 : Fin 4 → ℝ := Fin.snoc half_12_17_φ3 (53226836893/2500000000000 : ℝ)

theorem half_12_17_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_12_17_φ4) (74828821878677/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_17_φ4 (by norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_17_hF1 : SourcePowerBound (paddedMoment 18 0 1 16 half_12_17_φ4) (28276273959559/10000000000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_17_φ4 (by norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_17_hx4 : SourcePowerBound (powerBoxCross 18 8 16 half_12_17_φ4) (24457677537801/2500000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 8) (r := 1) (v := 2) (t := 11) (D := 16)
    (a := (1/22 : ℝ)) (b := (5/22 : ℝ)) (c := (8/11 : ℝ))
    (by norm_num) half_12_17_φ4 (by norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_17_hF1 half_12_17_hF2 half_11_17
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_17_hx3 : SourcePowerBound (powerBoxCross 18 9 8 half_12_17_φ3) (106579330456203/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (53226836893/2500000000000 : ℝ)) half_12_17_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_17
    (by simpa only [half_12_17_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_17_hx4)
  exact h.weaken (by norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_17_hx2 : SourcePowerBound (powerBoxCross 18 10 4 half_12_17_φ2) (5896047954537/500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (41178758719/1250000000000 : ℝ)) half_12_17_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_17 half_11_17
    (by simpa only [half_12_17_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_17_hx3)
  exact h.weaken (by norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_17_hx1 : SourcePowerBound (powerBoxCross 18 11 2 half_12_17_φ1) (131062570643339/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (45073358087/1250000000000 : ℝ)) half_12_17_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_17 half_12_16
    (by simpa only [half_12_17_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_17_hx2)
  exact h.weaken (by norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_17 : AdmissibleExponent 18 24 (34734087928013/2500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 10) (ψ := (374941955653/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_11_17
    (by simpa only [half_12_17_φ1] using half_12_17_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_17_φ1, half_12_17_φ2, half_12_17_φ3, half_12_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_13_17_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (96151103921/2500000000000 : ℝ)

def half_13_17_φ2 : Fin 2 → ℝ := Fin.snoc half_13_17_φ1 (74393681201/2000000000000 : ℝ)

def half_13_17_φ3 : Fin 3 → ℝ := Fin.snoc half_13_17_φ2 (87473288961/2500000000000 : ℝ)

def half_13_17_φ4 : Fin 4 → ℝ := Fin.snoc half_13_17_φ3 (35414158331/1250000000000 : ℝ)

theorem half_13_17_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_13_17_φ4) (69121258546769/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_17_φ4 (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_13_17_hx4 : SourcePowerBound (powerBoxCross 18 9 16 half_13_17_φ4) (107000764080359/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 16)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_13_17_φ4 (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_17_hF2 half_12_17 half_12_17
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_17_hx3 : SourcePowerBound (powerBoxCross 18 10 8 half_13_17_φ3) (117261145504261/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (35414158331/1250000000000 : ℝ)) half_13_17_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_17 half_11_17
    (by simpa only [half_13_17_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_17_hx4)
  exact h.weaken (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_17_hx2 : SourcePowerBound (powerBoxCross 18 11 4 half_13_17_φ2) (6486804561091/500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (87473288961/2500000000000 : ℝ)) half_13_17_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_17 half_12_17
    (by simpa only [half_13_17_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_17_hx3)
  exact h.weaken (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_17_hx1 : SourcePowerBound (powerBoxCross 18 12 2 half_13_17_φ1) (143977402691001/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (74393681201/2000000000000 : ℝ)) half_13_17_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_17 half_13_16
    (by simpa only [half_13_17_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_17_hx2)
  exact h.weaken (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_17 : AdmissibleExponent 18 26 (152823304251733/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 11) (ψ := (96151103921/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_12_17
    (by simpa only [half_13_17_φ1] using half_13_17_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_17_φ1, half_13_17_φ2, half_13_17_φ3, half_13_17_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_14_17_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (394360702169/10000000000000 : ℝ)

def half_14_17_φ2 : Fin 2 → ℝ := Fin.snoc half_14_17_φ1 (382996729509/10000000000000 : ℝ)

def half_14_17_φ3 : Fin 3 → ℝ := Fin.snoc half_14_17_φ2 (183630405157/5000000000000 : ℝ)

def half_14_17_φ4 : Fin 4 → ℝ := Fin.snoc half_14_17_φ3 (33211574759/1000000000000 : ℝ)

def half_14_17_φ5 : Fin 5 → ℝ := Fin.snoc half_14_17_φ4 (25697591847/1250000000000 : ℝ)

theorem half_14_17_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_14_17_φ5) (42100974528871/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_14_17_φ5 (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_14_17_hx5 : SourcePowerBound (powerBoxCross 18 9 32 half_14_17_φ5) (53861325390471/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_14_17_φ5 (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_17_hF2 half_12_17 half_12_17
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_17_hx4 : SourcePowerBound (powerBoxCross 18 10 16 half_14_17_φ4) (116492707666679/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (25697591847/1250000000000 : ℝ)) half_14_17_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_17 half_11_17
    (by simpa only [half_14_17_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_17_hx5)
  exact h.weaken (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_17_hx3 : SourcePowerBound (powerBoxCross 18 11 8 half_14_17_φ3) (128188920102267/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (33211574759/1000000000000 : ℝ)) half_14_17_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_17 half_12_17
    (by simpa only [half_14_17_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_17_hx4)
  exact h.weaken (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_17_hx2 : SourcePowerBound (powerBoxCross 18 12 4 half_14_17_φ2) (141814895951351/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (183630405157/5000000000000 : ℝ)) half_14_17_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_17 half_13_17
    (by simpa only [half_14_17_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_17_hx3)
  exact h.weaken (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_17_hx1 : SourcePowerBound (powerBoxCross 18 13 2 half_14_17_φ1) (157190914396671/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (382996729509/10000000000000 : ℝ)) half_14_17_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_17 half_14_16
    (by simpa only [half_14_17_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_17_hx2)
  exact h.weaken (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_17 : AdmissibleExponent 18 28 (10440620746931/625000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 12) (ψ := (394360702169/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_13_17
    (by simpa only [half_14_17_φ1] using half_14_17_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_17_φ1, half_14_17_φ2, half_14_17_φ3, half_14_17_φ4, half_14_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_15_17_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (201818855013/5000000000000 : ℝ)

def half_15_17_φ2 : Fin 2 → ℝ := Fin.snoc half_15_17_φ1 (196493776427/5000000000000 : ℝ)

def half_15_17_φ3 : Fin 3 → ℝ := Fin.snoc half_15_17_φ2 (23716094941/625000000000 : ℝ)

def half_15_17_φ4 : Fin 4 → ℝ := Fin.snoc half_15_17_φ3 (355225074781/10000000000000 : ℝ)

def half_15_17_φ5 : Fin 5 → ℝ := Fin.snoc half_15_17_φ4 (35536346781/1250000000000 : ℝ)

theorem half_15_17_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_15_17_φ5) (15480893964157/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_15_17_φ5 (by norm_num [half_15_17_φ1, half_15_17_φ2, half_15_17_φ3, half_15_17_φ4, half_15_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_17_φ1, half_15_17_φ2, half_15_17_φ3, half_15_17_φ4, half_15_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_17_φ1, half_15_17_φ2, half_15_17_φ3, half_15_17_φ4, half_15_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_15_17_φ1, half_15_17_φ2, half_15_17_φ3, half_15_17_φ4, half_15_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_15_17_hx5 : SourcePowerBound (powerBoxCross 18 10 32 half_15_17_φ5) (7254348298501/625000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_15_17_φ5 (by norm_num [half_15_17_φ1, half_15_17_φ2, half_15_17_φ3, half_15_17_φ4, half_15_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_17_φ1, half_15_17_φ2, half_15_17_φ3, half_15_17_φ4, half_15_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_15_17_hF2 half_13_17 half_14_17
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_17_φ1, half_15_17_φ2, half_15_17_φ3, half_15_17_φ4, half_15_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_17_hx4 : SourcePowerBound (powerBoxCross 18 11 16 half_15_17_φ4) (126549891469283/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (35536346781/1250000000000 : ℝ)) half_15_17_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_17_φ1, half_15_17_φ2, half_15_17_φ3, half_15_17_φ4, half_15_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_17_φ1, half_15_17_φ2, half_15_17_φ3, half_15_17_φ4, half_15_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_17_φ1, half_15_17_φ2, half_15_17_φ3, half_15_17_φ4, half_15_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_17 half_12_17
    (by simpa only [half_15_17_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_17_hx5)
  exact h.weaken (by norm_num [half_15_17_φ1, half_15_17_φ2, half_15_17_φ3, half_15_17_φ4, half_15_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_17_hx3 : SourcePowerBound (powerBoxCross 18 12 8 half_15_17_φ3) (69716557329401/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (355225074781/10000000000000 : ℝ)) half_15_17_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_17_φ1, half_15_17_φ2, half_15_17_φ3, half_15_17_φ4, half_15_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_17_φ1, half_15_17_φ2, half_15_17_φ3, half_15_17_φ4, half_15_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_17_φ1, half_15_17_φ2, half_15_17_φ3, half_15_17_φ4, half_15_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_17 half_13_17
    (by simpa only [half_15_17_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_17_hx4)
  exact h.weaken (by norm_num [half_15_17_φ1, half_15_17_φ2, half_15_17_φ3, half_15_17_φ4, half_15_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_17_hx2 : SourcePowerBound (powerBoxCross 18 13 4 half_15_17_φ2) (15418016024179/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (23716094941/625000000000 : ℝ)) half_15_17_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_17_φ1, half_15_17_φ2, half_15_17_φ3, half_15_17_φ4, half_15_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_17_φ1, half_15_17_φ2, half_15_17_φ3, half_15_17_φ4, half_15_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_17_φ1, half_15_17_φ2, half_15_17_φ3, half_15_17_φ4, half_15_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_17 half_14_17
    (by simpa only [half_15_17_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_17_hx3)
  exact h.weaken (by norm_num [half_15_17_φ1, half_15_17_φ2, half_15_17_φ3, half_15_17_φ4, half_15_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_17_hx1 : SourcePowerBound (powerBoxCross 18 14 2 half_15_17_φ1) (170710804461667/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (196493776427/5000000000000 : ℝ)) half_15_17_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_17_φ1, half_15_17_φ2, half_15_17_φ3, half_15_17_φ4, half_15_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_17_φ1, half_15_17_φ2, half_15_17_φ3, half_15_17_φ4, half_15_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_17_φ1, half_15_17_φ2, half_15_17_φ3, half_15_17_φ4, half_15_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_17 half_15_16
    (by simpa only [half_15_17_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_17_hx2)
  exact h.weaken (by norm_num [half_15_17_φ1, half_15_17_φ2, half_15_17_φ3, half_15_17_φ4, half_15_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_17 : AdmissibleExponent 18 30 (181609022632369/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 13) (ψ := (201818855013/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_14_17
    (by simpa only [half_15_17_φ1] using half_15_17_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_17_φ1, half_15_17_φ2, half_15_17_φ3, half_15_17_φ4, half_15_17_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_16_17_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (412888818833/10000000000000 : ℝ)

def half_16_17_φ2 : Fin 2 → ℝ := Fin.snoc half_16_17_φ1 (10067360853/250000000000 : ℝ)

def half_16_17_φ3 : Fin 3 → ℝ := Fin.snoc half_16_17_φ2 (39109731279/1000000000000 : ℝ)

def half_16_17_φ4 : Fin 4 → ℝ := Fin.snoc half_16_17_φ3 (374102469717/10000000000000 : ℝ)

def half_16_17_φ5 : Fin 5 → ℝ := Fin.snoc half_16_17_φ4 (168150710119/5000000000000 : ℝ)

def half_16_17_φ6 : Fin 6 → ℝ := Fin.snoc half_16_17_φ5 (26028086239/1250000000000 : ℝ)

theorem half_16_17_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_16_17_φ6) (9160923357389/1000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_16_17_φ6 (by norm_num [half_16_17_φ1, half_16_17_φ2, half_16_17_φ3, half_16_17_φ4, half_16_17_φ5, half_16_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_17_φ1, half_16_17_φ2, half_16_17_φ3, half_16_17_φ4, half_16_17_φ5, half_16_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_17_φ1, half_16_17_φ2, half_16_17_φ3, half_16_17_φ4, half_16_17_φ5, half_16_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_16_17_φ1, half_16_17_φ2, half_16_17_φ3, half_16_17_φ4, half_16_17_φ5, half_16_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_16_17_hx6 : SourcePowerBound (powerBoxCross 18 10 64 half_16_17_φ6) (115960786493917/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_16_17_φ6 (by norm_num [half_16_17_φ1, half_16_17_φ2, half_16_17_φ3, half_16_17_φ4, half_16_17_φ5, half_16_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_17_φ1, half_16_17_φ2, half_16_17_φ3, half_16_17_φ4, half_16_17_φ5, half_16_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_16_17_hF2 half_13_17 half_14_17
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_17_φ1, half_16_17_φ2, half_16_17_φ3, half_16_17_φ4, half_16_17_φ5, half_16_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_17_hx5 : SourcePowerBound (powerBoxCross 18 11 32 half_16_17_φ5) (124813849773789/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 11) (u := 9) (t := 12)
    (D := 32) (ψ := (26028086239/1250000000000 : ℝ)) half_16_17_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_17_φ1, half_16_17_φ2, half_16_17_φ3, half_16_17_φ4, half_16_17_φ5, half_16_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_17_φ1, half_16_17_φ2, half_16_17_φ3, half_16_17_φ4, half_16_17_φ5, half_16_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_17_φ1, half_16_17_φ2, half_16_17_φ3, half_16_17_φ4, half_16_17_φ5, half_16_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_17 half_12_17
    (by simpa only [half_16_17_φ6, show (2:ℝ)*32=64 by norm_num] using half_16_17_hx6)
  exact h.weaken (by norm_num [half_16_17_φ1, half_16_17_φ2, half_16_17_φ3, half_16_17_φ4, half_16_17_φ5, half_16_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_17_hx4 : SourcePowerBound (powerBoxCross 18 12 16 half_16_17_φ4) (68417030892323/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (168150710119/5000000000000 : ℝ)) half_16_17_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_17_φ1, half_16_17_φ2, half_16_17_φ3, half_16_17_φ4, half_16_17_φ5, half_16_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_17_φ1, half_16_17_φ2, half_16_17_φ3, half_16_17_φ4, half_16_17_φ5, half_16_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_17_φ1, half_16_17_φ2, half_16_17_φ3, half_16_17_φ4, half_16_17_φ5, half_16_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_17 half_13_17
    (by simpa only [half_16_17_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_17_hx5)
  exact h.weaken (by norm_num [half_16_17_φ1, half_16_17_φ2, half_16_17_φ3, half_16_17_φ4, half_16_17_φ5, half_16_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_17_hx3 : SourcePowerBound (powerBoxCross 18 13 8 half_16_17_φ3) (15090859514101/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (374102469717/10000000000000 : ℝ)) half_16_17_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_17_φ1, half_16_17_φ2, half_16_17_φ3, half_16_17_φ4, half_16_17_φ5, half_16_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_17_φ1, half_16_17_φ2, half_16_17_φ3, half_16_17_φ4, half_16_17_φ5, half_16_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_17_φ1, half_16_17_φ2, half_16_17_φ3, half_16_17_φ4, half_16_17_φ5, half_16_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_17 half_14_17
    (by simpa only [half_16_17_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_17_hx4)
  exact h.weaken (by norm_num [half_16_17_φ1, half_16_17_φ2, half_16_17_φ3, half_16_17_φ4, half_16_17_φ5, half_16_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_17_hx2 : SourcePowerBound (powerBoxCross 18 14 4 half_16_17_φ2) (83404601887129/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (39109731279/1000000000000 : ℝ)) half_16_17_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_17_φ1, half_16_17_φ2, half_16_17_φ3, half_16_17_φ4, half_16_17_φ5, half_16_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_17_φ1, half_16_17_φ2, half_16_17_φ3, half_16_17_φ4, half_16_17_φ5, half_16_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_17_φ1, half_16_17_φ2, half_16_17_φ3, half_16_17_φ4, half_16_17_φ5, half_16_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_17 half_15_17
    (by simpa only [half_16_17_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_17_hx3)
  exact h.weaken (by norm_num [half_16_17_φ1, half_16_17_φ2, half_16_17_φ3, half_16_17_φ4, half_16_17_φ5, half_16_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_17_hx1 : SourcePowerBound (powerBoxCross 18 15 2 half_16_17_φ1) (92261738983403/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (10067360853/250000000000 : ℝ)) half_16_17_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_17_φ1, half_16_17_φ2, half_16_17_φ3, half_16_17_φ4, half_16_17_φ5, half_16_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_17_φ1, half_16_17_φ2, half_16_17_φ3, half_16_17_φ4, half_16_17_φ5, half_16_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_17_φ1, half_16_17_φ2, half_16_17_φ3, half_16_17_φ4, half_16_17_φ5, half_16_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_17 half_16_16
    (by simpa only [half_16_17_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_17_hx2)
  exact h.weaken (by norm_num [half_16_17_φ1, half_16_17_φ2, half_16_17_φ3, half_16_17_φ4, half_16_17_φ5, half_16_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_17 : AdmissibleExponent 18 32 (196497253712963/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 14) (ψ := (412888818833/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_15_17
    (by simpa only [half_16_17_φ1] using half_16_17_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_17_φ1, half_16_17_φ2, half_16_17_φ3, half_16_17_φ4, half_16_17_φ5, half_16_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_17_17_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (42182631413/1000000000000 : ℝ)

def half_17_17_φ2 : Fin 2 → ℝ := Fin.snoc half_17_17_φ1 (412010864473/10000000000000 : ℝ)

def half_17_17_φ3 : Fin 3 → ℝ := Fin.snoc half_17_17_φ2 (401123766487/10000000000000 : ℝ)

def half_17_17_φ4 : Fin 4 → ℝ := Fin.snoc half_17_17_φ3 (387122448789/10000000000000 : ℝ)

def half_17_17_φ5 : Fin 5 → ℝ := Fin.snoc half_17_17_φ4 (361339730193/10000000000000 : ℝ)

def half_17_17_φ6 : Fin 6 → ℝ := Fin.snoc half_17_17_φ5 (112962387/3906250000 : ℝ)

theorem half_17_17_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_17_17_φ6) (10512131428201/1250000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_17_17_φ6 (by norm_num [half_17_17_φ1, half_17_17_φ2, half_17_17_φ3, half_17_17_φ4, half_17_17_φ5, half_17_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_17_φ1, half_17_17_φ2, half_17_17_φ3, half_17_17_φ4, half_17_17_φ5, half_17_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_17_φ1, half_17_17_φ2, half_17_17_φ3, half_17_17_φ4, half_17_17_φ5, half_17_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_17_17_φ1, half_17_17_φ2, half_17_17_φ3, half_17_17_φ4, half_17_17_φ5, half_17_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_17_17_hx6 : SourcePowerBound (powerBoxCross 18 11 64 half_17_17_φ6) (61731995714011/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 11) (r := 2) (v := 14) (w := 15) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_17_17_φ6 (by norm_num [half_17_17_φ1, half_17_17_φ2, half_17_17_φ3, half_17_17_φ4, half_17_17_φ5, half_17_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_17_φ1, half_17_17_φ2, half_17_17_φ3, half_17_17_φ4, half_17_17_φ5, half_17_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_17_17_hF2 half_14_17 half_15_17
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_17_φ1, half_17_17_φ2, half_17_17_φ3, half_17_17_φ4, half_17_17_φ5, half_17_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_17_hx5 : SourcePowerBound (powerBoxCross 18 12 32 half_17_17_φ5) (134165316470327/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 12) (u := 10) (t := 13)
    (D := 32) (ψ := (112962387/3906250000 : ℝ)) half_17_17_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_17_φ1, half_17_17_φ2, half_17_17_φ3, half_17_17_φ4, half_17_17_φ5, half_17_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_17_φ1, half_17_17_φ2, half_17_17_φ3, half_17_17_φ4, half_17_17_φ5, half_17_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_17_φ1, half_17_17_φ2, half_17_17_φ3, half_17_17_φ4, half_17_17_φ5, half_17_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_17 half_13_17
    (by simpa only [half_17_17_φ6, show (2:ℝ)*32=64 by norm_num] using half_17_17_hx6)
  exact h.weaken (by norm_num [half_17_17_φ1, half_17_17_φ2, half_17_17_φ3, half_17_17_φ4, half_17_17_φ5, half_17_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_17_hx4 : SourcePowerBound (powerBoxCross 18 13 16 half_17_17_φ4) (1151772470559/78125000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (361339730193/10000000000000 : ℝ)) half_17_17_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_17_φ1, half_17_17_φ2, half_17_17_φ3, half_17_17_φ4, half_17_17_φ5, half_17_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_17_φ1, half_17_17_φ2, half_17_17_φ3, half_17_17_φ4, half_17_17_φ5, half_17_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_17_φ1, half_17_17_φ2, half_17_17_φ3, half_17_17_φ4, half_17_17_φ5, half_17_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_17 half_14_17
    (by simpa only [half_17_17_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_17_hx5)
  exact h.weaken (by norm_num [half_17_17_φ1, half_17_17_φ2, half_17_17_φ3, half_17_17_φ4, half_17_17_φ5, half_17_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_17_hx3 : SourcePowerBound (powerBoxCross 18 14 8 half_17_17_φ3) (162645809497211/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (387122448789/10000000000000 : ℝ)) half_17_17_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_17_φ1, half_17_17_φ2, half_17_17_φ3, half_17_17_φ4, half_17_17_φ5, half_17_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_17_φ1, half_17_17_φ2, half_17_17_φ3, half_17_17_φ4, half_17_17_φ5, half_17_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_17_φ1, half_17_17_φ2, half_17_17_φ3, half_17_17_φ4, half_17_17_φ5, half_17_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_17 half_15_17
    (by simpa only [half_17_17_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_17_hx4)
  exact h.weaken (by norm_num [half_17_17_φ1, half_17_17_φ2, half_17_17_φ3, half_17_17_φ4, half_17_17_φ5, half_17_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_17_hx2 : SourcePowerBound (powerBoxCross 18 15 4 half_17_17_φ2) (89853375326287/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (401123766487/10000000000000 : ℝ)) half_17_17_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_17_φ1, half_17_17_φ2, half_17_17_φ3, half_17_17_φ4, half_17_17_φ5, half_17_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_17_φ1, half_17_17_φ2, half_17_17_φ3, half_17_17_φ4, half_17_17_φ5, half_17_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_17_φ1, half_17_17_φ2, half_17_17_φ3, half_17_17_φ4, half_17_17_φ5, half_17_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_17 half_16_17
    (by simpa only [half_17_17_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_17_hx3)
  exact h.weaken (by norm_num [half_17_17_φ1, half_17_17_φ2, half_17_17_φ3, half_17_17_φ4, half_17_17_φ5, half_17_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_17_hx1 : SourcePowerBound (powerBoxCross 18 16 2 half_17_17_φ1) (9931515440003/500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (412010864473/10000000000000 : ℝ)) half_17_17_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_17_φ1, half_17_17_φ2, half_17_17_φ3, half_17_17_φ4, half_17_17_φ5, half_17_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_17_φ1, half_17_17_φ2, half_17_17_φ3, half_17_17_φ4, half_17_17_φ5, half_17_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_17_φ1, half_17_17_φ2, half_17_17_φ3, half_17_17_φ4, half_17_17_φ5, half_17_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_15_17 half_17_16
    (by simpa only [half_17_17_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_17_hx2)
  exact h.weaken (by norm_num [half_17_17_φ1, half_17_17_φ2, half_17_17_φ3, half_17_17_φ4, half_17_17_φ5, half_17_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_17 : AdmissibleExponent 18 34 (21170692453809/1000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 15) (ψ := (42182631413/1000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_16_17
    (by simpa only [half_17_17_φ1] using half_17_17_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_17_φ1, half_17_17_φ2, half_17_17_φ3, half_17_17_φ4, half_17_17_φ5, half_17_17_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])


end Waring.SeedCompletionHigher18SimpleSeeds
