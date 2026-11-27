import Waring.SeedCompletionHigher18SimpleSeedsC11

noncomputable section
set_option maxHeartbeats 2000000
namespace Waring.SeedCompletionHigher18SimpleSeeds
open SmoothMoments FirstStageTransport SeedCompletionNaturalBox
open SeedCompletionSourceBounds SeedCompletionPaddedSource SeedCompletionGeneralTerminal
open PolicyCompletionMajorPowerRanges

def half_9_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (21489927449/625000000000 : ℝ)

def half_9_12_φ2 : Fin 2 → ℝ := Fin.snoc half_9_12_φ1 (308345154213/10000000000000 : ℝ)

def half_9_12_φ3 : Fin 3 → ℝ := Fin.snoc half_9_12_φ2 (16805747143/1250000000000 : ℝ)

theorem half_9_12_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_9_12_φ3) (69881871502409/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_12_φ3 (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_12_hF1 : SourcePowerBound (paddedMoment 18 0 1 8 half_9_12_φ3) (26627290500803/10000000000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_9_12_φ3 (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_9_12_hx3 : SourcePowerBound (powerBoxCross 18 6 8 half_9_12_φ3) (76993036281077/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 6) (r := 1) (v := 2) (t := 10) (D := 8)
    (a := (3/10 : ℝ)) (b := (1/10 : ℝ)) (c := (3/5 : ℝ))
    (by norm_num) half_9_12_φ3 (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_9_12_hF1 half_9_12_hF2 half_10_11
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_12_hx2 : SourcePowerBound (powerBoxCross 18 7 4 half_9_12_φ2) (84269421509659/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 7) (u := 5) (t := 8)
    (D := 4) (ψ := (16805747143/1250000000000 : ℝ)) half_9_12_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_6 SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_9_12_hx3)
  exact h.weaken (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_12_hx1 : SourcePowerBound (powerBoxCross 18 8 2 half_9_12_φ1) (18834959595667/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 8) (u := 6) (t := 9)
    (D := 2) (ψ := (308345154213/10000000000000 : ℝ)) half_9_12_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_11
    (by simpa only [half_9_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_9_12_hx2)
  exact h.weaken (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_9_12 : AdmissibleExponent 18 18 (19866476113219/2000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 7) (ψ := (21489927449/625000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8
    (by simpa only [half_9_12_φ1] using half_9_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_9_12_φ1, half_9_12_φ2, half_9_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_10_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (353748876737/10000000000000 : ℝ)

def half_10_12_φ2 : Fin 2 → ℝ := Fin.snoc half_10_12_φ1 (164628287069/5000000000000 : ℝ)

def half_10_12_φ3 : Fin 3 → ℝ := Fin.snoc half_10_12_φ2 (4598776273/200000000000 : ℝ)

theorem half_10_12_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_10_12_φ3) (2537593700369/400000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_10_12_φ3 (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_10_12_hx3 : SourcePowerBound (powerBoxCross 18 7 8 half_10_12_φ3) (43238956514147/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 7) (r := 2) (v := 9) (w := 10) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_10_12_φ3 (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_10_12_hF2 half_9_12 half_10_11
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_12_hx2 : SourcePowerBound (powerBoxCross 18 8 4 half_10_12_φ2) (95201974884731/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 8) (u := 6) (t := 9)
    (D := 4) (ψ := (4598776273/200000000000 : ℝ)) half_10_12_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_7 half_9_12
    (by simpa only [half_10_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_10_12_hx3)
  exact h.weaken (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_12_hx1 : SourcePowerBound (powerBoxCross 18 9 2 half_10_12_φ1) (26543064409491/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 9) (u := 7) (t := 10)
    (D := 2) (ψ := (164628287069/5000000000000 : ℝ)) half_10_12_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_11
    (by simpa only [half_10_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_10_12_hx2)
  exact h.weaken (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_10_12 : AdmissibleExponent 18 20 (112185988542493/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 8) (ψ := (353748876737/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_9_12
    (by simpa only [half_10_12_φ1] using half_10_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_10_12_φ1, half_10_12_φ2, half_10_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_11_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (364748354939/10000000000000 : ℝ)

def half_11_12_φ2 : Fin 2 → ℝ := Fin.snoc half_11_12_φ1 (69278986443/2000000000000 : ℝ)

def half_11_12_φ3 : Fin 3 → ℝ := Fin.snoc half_11_12_φ2 (294728838211/10000000000000 : ℝ)

theorem half_11_12_hF2 : SourcePowerBound (paddedMoment 18 0 2 8 half_11_12_φ3) (11740104321277/2000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 3) (r := 0) (D := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_11_12_φ3 (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_11_12_hx3 : SourcePowerBound (powerBoxCross 18 8 8 half_11_12_φ3) (19257748366763/2000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 8) (r := 2) (v := 10) (w := 11) (D := 8)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_11_12_φ3 (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_11_12_hF2 half_10_12 half_11_11
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_12_hx2 : SourcePowerBound (powerBoxCross 18 9 4 half_11_12_φ2) (26603524475173/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 9) (u := 7) (t := 10)
    (D := 4) (ψ := (294728838211/10000000000000 : ℝ)) half_11_12_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_12
    (by simpa only [half_11_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_11_12_hx3)
  exact h.weaken (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_12_hx1 : SourcePowerBound (powerBoxCross 18 10 2 half_11_12_φ1) (29614692855157/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 10) (u := 8) (t := 11)
    (D := 2) (ψ := (69278986443/2000000000000 : ℝ)) half_11_12_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_12 half_11_11
    (by simpa only [half_11_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_11_12_hx2)
  exact h.weaken (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_11_12 : AdmissibleExponent 18 22 (125388990164469/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 9) (ψ := (364748354939/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_10_12
    (by simpa only [half_11_12_φ1] using half_11_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_11_12_φ1, half_11_12_φ2, half_11_12_φ3, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_12_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (374942712481/10000000000000 : ℝ)

def half_12_12_φ2 : Fin 2 → ℝ := Fin.snoc half_12_12_φ1 (360586925099/10000000000000 : ℝ)

def half_12_12_φ3 : Fin 3 → ℝ := Fin.snoc half_12_12_φ2 (32943014989/1000000000000 : ℝ)

def half_12_12_φ4 : Fin 4 → ℝ := Fin.snoc half_12_12_φ3 (212907723623/10000000000000 : ℝ)

theorem half_12_12_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_12_12_φ4) (74828756934257/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_12_φ4 (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_12_hF1 : SourcePowerBound (paddedMoment 18 0 1 16 half_12_12_φ4) (28276252311419/10000000000000 : ℝ) := by
  have h := padded_second_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_12_12_φ4 (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_12_12_hx4 : SourcePowerBound (powerBoxCross 18 8 16 half_12_12_φ4) (97830684216651/10000000000000 : ℝ) := by
  have h := full_B_cross_power (k := 18) (s := 8) (r := 1) (v := 2) (t := 11) (D := 16)
    (a := (1/22 : ℝ)) (b := (5/22 : ℝ)) (c := (8/11 : ℝ))
    (by norm_num) half_12_12_φ4 (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_12_12_hF1 half_12_12_hF2 half_11_12
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_12_hx3 : SourcePowerBound (powerBoxCross 18 9 8 half_12_12_φ3) (26644826946871/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 9) (u := 7) (t := 10)
    (D := 8) (ψ := (212907723623/10000000000000 : ℝ)) half_12_12_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) SeedCompletionEven18SecondSeeds.degree18_half_8 half_10_12
    (by simpa only [half_12_12_φ4, show (2:ℝ)*8=16 by norm_num] using half_12_12_hx4)
  exact h.weaken (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_12_hx2 : SourcePowerBound (powerBoxCross 18 10 4 half_12_12_φ2) (58960468703001/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 10) (u := 8) (t := 11)
    (D := 4) (ψ := (32943014989/1000000000000 : ℝ)) half_12_12_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_12 half_11_12
    (by simpa only [half_12_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_12_12_hx3)
  exact h.weaken (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_12_hx1 : SourcePowerBound (powerBoxCross 18 11 2 half_12_12_φ1) (13106256406821/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 11) (u := 9) (t := 12)
    (D := 2) (ψ := (360586925099/10000000000000 : ℝ)) half_12_12_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_12 half_12_11
    (by simpa only [half_12_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_12_12_hx2)
  exact h.weaken (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_12_12 : AdmissibleExponent 18 24 (138936361030311/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 10) (ψ := (374942712481/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_11_12
    (by simpa only [half_12_12_φ1] using half_12_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_12_12_φ1, half_12_12_φ2, half_12_12_φ3, half_12_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_13_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (96151771327/2500000000000 : ℝ)

def half_13_12_φ2 : Fin 2 → ℝ := Fin.snoc half_13_12_φ1 (92992153391/2500000000000 : ℝ)

def half_13_12_φ3 : Fin 3 → ℝ := Fin.snoc half_13_12_φ2 (349893477541/10000000000000 : ℝ)

def half_13_12_φ4 : Fin 4 → ℝ := Fin.snoc half_13_12_φ3 (283314530897/10000000000000 : ℝ)

theorem half_13_12_hF2 : SourcePowerBound (paddedMoment 18 0 2 16 half_13_12_φ4) (6912103092719/1000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 4) (r := 0) (D := 16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_13_12_φ4 (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_13_12_hx4 : SourcePowerBound (powerBoxCross 18 9 16 half_13_12_φ4) (53500333343033/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 16)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_13_12_φ4 (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_13_12_hF2 half_12_12 half_12_12
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_12_hx3 : SourcePowerBound (powerBoxCross 18 10 8 half_13_12_φ3) (23452212260891/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 10) (u := 8) (t := 11)
    (D := 8) (ψ := (283314530897/10000000000000 : ℝ)) half_13_12_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_12 half_11_12
    (by simpa only [half_13_12_φ4, show (2:ℝ)*8=16 by norm_num] using half_13_12_hx4)
  exact h.weaken (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_12_hx2 : SourcePowerBound (powerBoxCross 18 11 4 half_13_12_φ2) (129736012041349/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 11) (u := 9) (t := 12)
    (D := 4) (ψ := (349893477541/10000000000000 : ℝ)) half_13_12_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_12 half_12_12
    (by simpa only [half_13_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_13_12_hx3)
  exact h.weaken (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_12_hx1 : SourcePowerBound (powerBoxCross 18 12 2 half_13_12_φ1) (8998586076857/625000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 12) (u := 10) (t := 13)
    (D := 2) (ψ := (92992153391/2500000000000 : ℝ)) half_13_12_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_12 half_13_11
    (by simpa only [half_13_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_13_12_hx2)
  exact h.weaken (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_13_12 : AdmissibleExponent 18 26 (38205835047949/2500000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 11) (ψ := (96151771327/2500000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_12_12
    (by simpa only [half_13_12_φ1] using half_13_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_13_12_φ1, half_13_12_φ2, half_13_12_φ3, half_13_12_φ4, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_14_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (394368525903/10000000000000 : ℝ)

def half_14_12_φ2 : Fin 2 → ℝ := Fin.snoc half_14_12_φ1 (382997294313/10000000000000 : ℝ)

def half_14_12_φ3 : Fin 3 → ℝ := Fin.snoc half_14_12_φ2 (73452218591/2000000000000 : ℝ)

def half_14_12_φ4 : Fin 4 → ℝ := Fin.snoc half_14_12_φ3 (332116422493/10000000000000 : ℝ)

def half_14_12_φ5 : Fin 5 → ℝ := Fin.snoc half_14_12_φ4 (205583609579/10000000000000 : ℝ)

theorem half_14_12_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_14_12_φ5) (84201325792607/10000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_14_12_φ5 (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_14_12_hx5 : SourcePowerBound (powerBoxCross 18 9 32 half_14_12_φ5) (53861186716619/5000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 9) (r := 2) (v := 12) (w := 12) (D := 32)
    (a := (1/4 : ℝ)) (b := (3/4 : ℝ)) (c := (0/1 : ℝ))
    (by norm_num) half_14_12_φ5 (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_14_12_hF2 half_12_12 half_12_12
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_12_hx4 : SourcePowerBound (powerBoxCross 18 10 16 half_14_12_φ4) (116492456347581/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 10) (u := 8) (t := 11)
    (D := 16) (ψ := (205583609579/10000000000000 : ℝ)) half_14_12_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_9_12 half_11_12
    (by simpa only [half_14_12_φ5, show (2:ℝ)*16=32 by norm_num] using half_14_12_hx5)
  exact h.weaken (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_12_hx3 : SourcePowerBound (powerBoxCross 18 11 8 half_14_12_φ3) (12818867103801/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 11) (u := 9) (t := 12)
    (D := 8) (ψ := (332116422493/10000000000000 : ℝ)) half_14_12_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_12 half_12_12
    (by simpa only [half_14_12_φ4, show (2:ℝ)*8=16 by norm_num] using half_14_12_hx4)
  exact h.weaken (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_12_hx2 : SourcePowerBound (powerBoxCross 18 12 4 half_14_12_φ2) (70907327779639/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 12) (u := 10) (t := 13)
    (D := 4) (ψ := (73452218591/2000000000000 : ℝ)) half_14_12_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_12 half_13_12
    (by simpa only [half_14_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_14_12_hx3)
  exact h.weaken (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_12_hx1 : SourcePowerBound (powerBoxCross 18 13 2 half_14_12_φ1) (31438167435643/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 13) (u := 11) (t := 14)
    (D := 2) (ψ := (382997294313/10000000000000 : ℝ)) half_14_12_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_12 half_14_11
    (by simpa only [half_14_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_14_12_hx2)
  exact h.weaken (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_14_12 : AdmissibleExponent 18 28 (16705005032579/1000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 12) (ψ := (394368525903/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_13_12
    (by simpa only [half_14_12_φ1] using half_14_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_14_12_φ1, half_14_12_φ2, half_14_12_φ3, half_14_12_φ4, half_14_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_15_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (201829070399/5000000000000 : ℝ)

def half_15_12_φ2 : Fin 2 → ℝ := Fin.snoc half_15_12_φ1 (39298924929/1000000000000 : ℝ)

def half_15_12_φ3 : Fin 3 → ℝ := Fin.snoc half_15_12_φ2 (47432323587/1250000000000 : ℝ)

def half_15_12_φ4 : Fin 4 → ℝ := Fin.snoc half_15_12_φ3 (355227413591/10000000000000 : ℝ)

def half_15_12_φ5 : Fin 5 → ℝ := Fin.snoc half_15_12_φ4 (284299967197/10000000000000 : ℝ)

theorem half_15_12_hF2 : SourcePowerBound (paddedMoment 18 0 2 32 half_15_12_φ5) (19350674665457/2500000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 5) (r := 0) (D := 32)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_15_12_φ5 (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_15_12_hx5 : SourcePowerBound (powerBoxCross 18 10 32 half_15_12_φ5) (116068758511889/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 32)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_15_12_φ5 (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_15_12_hF2 half_13_12 half_14_12
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_12_hx4 : SourcePowerBound (powerBoxCross 18 11 16 half_15_12_φ4) (25309836234249/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 11) (u := 9) (t := 12)
    (D := 16) (ψ := (284299967197/10000000000000 : ℝ)) half_15_12_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_12 half_12_12
    (by simpa only [half_15_12_φ5, show (2:ℝ)*16=32 by norm_num] using half_15_12_hx5)
  exact h.weaken (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_12_hx3 : SourcePowerBound (powerBoxCross 18 12 8 half_15_12_φ3) (139432425499697/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 12) (u := 10) (t := 13)
    (D := 8) (ψ := (355227413591/10000000000000 : ℝ)) half_15_12_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_12 half_13_12
    (by simpa only [half_15_12_φ4, show (2:ℝ)*8=16 by norm_num] using half_15_12_hx4)
  exact h.weaken (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_12_hx2 : SourcePowerBound (powerBoxCross 18 13 4 half_15_12_φ2) (30835901907339/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 13) (u := 11) (t := 14)
    (D := 4) (ψ := (47432323587/1250000000000 : ℝ)) half_15_12_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_12 half_14_12
    (by simpa only [half_15_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_15_12_hx3)
  exact h.weaken (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_12_hx1 : SourcePowerBound (powerBoxCross 18 14 2 half_15_12_φ1) (170710597193123/10000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 14) (u := 12) (t := 15)
    (D := 2) (ψ := (39298924929/1000000000000 : ℝ)) half_15_12_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_12 half_15_11
    (by simpa only [half_15_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_15_12_hx2)
  exact h.weaken (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_15_12 : AdmissibleExponent 18 30 (181609366994669/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 13) (ψ := (201829070399/5000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_14_12
    (by simpa only [half_15_12_φ1] using half_15_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_15_12_φ1, half_15_12_φ2, half_15_12_φ3, half_15_12_φ4, half_15_12_φ5, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_16_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (412935570713/10000000000000 : ℝ)

def half_16_12_φ2 : Fin 2 → ℝ := Fin.snoc half_16_12_φ1 (201349263649/5000000000000 : ℝ)

def half_16_12_φ3 : Fin 3 → ℝ := Fin.snoc half_16_12_φ2 (391099048847/10000000000000 : ℝ)

def half_16_12_φ4 : Fin 4 → ℝ := Fin.snoc half_16_12_φ3 (37410400883/1000000000000 : ℝ)

def half_16_12_φ5 : Fin 5 → ℝ := Fin.snoc half_16_12_φ4 (42038217447/1250000000000 : ℝ)

def half_16_12_φ6 : Fin 6 → ℝ := Fin.snoc half_16_12_φ5 (104121076777/5000000000000 : ℝ)

theorem half_16_12_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_16_12_φ6) (45802681255141/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_16_12_φ6 (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, half_16_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, half_16_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, half_16_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, half_16_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_16_12_hx6 : SourcePowerBound (powerBoxCross 18 10 64 half_16_12_φ6) (23191791840609/2000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 10) (r := 2) (v := 13) (w := 14) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/2 : ℝ)) (c := (1/4 : ℝ))
    (by norm_num) half_16_12_φ6 (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, half_16_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, half_16_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_16_12_hF2 half_13_12 half_14_12
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, half_16_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_12_hx5 : SourcePowerBound (powerBoxCross 18 11 32 half_16_12_φ5) (62406101546773/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 11) (u := 9) (t := 12)
    (D := 32) (ψ := (104121076777/5000000000000 : ℝ)) half_16_12_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, half_16_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, half_16_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, half_16_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_10_12 half_12_12
    (by simpa only [half_16_12_φ6, show (2:ℝ)*32=64 by norm_num] using half_16_12_hx6)
  exact h.weaken (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, half_16_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_12_hx4 : SourcePowerBound (powerBoxCross 18 12 16 half_16_12_φ4) (27366485072659/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 12) (u := 10) (t := 13)
    (D := 16) (ψ := (42038217447/1250000000000 : ℝ)) half_16_12_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, half_16_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, half_16_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, half_16_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_12 half_13_12
    (by simpa only [half_16_12_φ5, show (2:ℝ)*16=32 by norm_num] using half_16_12_hx5)
  exact h.weaken (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, half_16_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_12_hx3 : SourcePowerBound (powerBoxCross 18 13 8 half_16_12_φ3) (75453480276087/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 13) (u := 11) (t := 14)
    (D := 8) (ψ := (37410400883/1000000000000 : ℝ)) half_16_12_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, half_16_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, half_16_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, half_16_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_12 half_14_12
    (by simpa only [half_16_12_φ4, show (2:ℝ)*8=16 by norm_num] using half_16_12_hx4)
  exact h.weaken (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, half_16_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_12_hx2 : SourcePowerBound (powerBoxCross 18 14 4 half_16_12_φ2) (41701918109741/2500000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 14) (u := 12) (t := 15)
    (D := 4) (ψ := (391099048847/10000000000000 : ℝ)) half_16_12_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, half_16_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, half_16_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, half_16_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_12 half_15_12
    (by simpa only [half_16_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_16_12_hx3)
  exact h.weaken (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, half_16_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_12_hx1 : SourcePowerBound (powerBoxCross 18 15 2 half_16_12_φ1) (2306537572559/125000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 15) (u := 13) (t := 16)
    (D := 2) (ψ := (201349263649/5000000000000 : ℝ)) half_16_12_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, half_16_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, half_16_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, half_16_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_12 half_16_11
    (by simpa only [half_16_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_16_12_hx2)
  exact h.weaken (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, half_16_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_16_12 : AdmissibleExponent 18 32 (196498137355397/10000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 14) (ψ := (412935570713/10000000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_15_12
    (by simpa only [half_16_12_φ1] using half_16_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_16_12_φ1, half_16_12_φ2, half_16_12_φ3, half_16_12_φ4, half_16_12_φ5, half_16_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

def half_17_12_φ1 : Fin 1 → ℝ := Fin.snoc emptyPhi (26370198867/625000000000 : ℝ)

def half_17_12_φ2 : Fin 2 → ℝ := Fin.snoc half_17_12_φ1 (25751254327/625000000000 : ℝ)

def half_17_12_φ3 : Fin 3 → ℝ := Fin.snoc half_17_12_φ2 (80225681939/2000000000000 : ℝ)

def half_17_12_φ4 : Fin 4 → ℝ := Fin.snoc half_17_12_φ3 (193563389273/5000000000000 : ℝ)

def half_17_12_φ5 : Fin 5 → ℝ := Fin.snoc half_17_12_φ4 (180675473283/5000000000000 : ℝ)

def half_17_12_φ6 : Fin 6 → ℝ := Fin.snoc half_17_12_φ5 (289225193571/10000000000000 : ℝ)

theorem half_17_12_hF2 : SourcePowerBound (paddedMoment 18 0 2 64 half_17_12_φ6) (42044248223209/5000000000000 : ℝ) := by
  have h := padded_fourth_power (k := 18) (j := 6) (r := 0) (D := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) half_17_12_φ6 (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, half_17_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, half_17_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, half_17_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
  convert h using 1 <;> norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, half_17_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]

theorem half_17_12_hx6 : SourcePowerBound (powerBoxCross 18 11 64 half_17_12_φ6) (123459784858281/10000000000000 : ℝ) := by
  have h := full_A_cross_power (k := 18) (s := 11) (r := 2) (v := 14) (w := 15) (D := 64)
    (a := (1/4 : ℝ)) (b := (1/4 : ℝ)) (c := (1/2 : ℝ))
    (by norm_num) half_17_12_φ6 (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, half_17_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, half_17_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) half_17_12_hF2 half_14_12 half_15_12
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact h.weaken (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, half_17_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_12_hx5 : SourcePowerBound (powerBoxCross 18 12 32 half_17_12_φ5) (1048137696467/78125000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 5) (s := 12) (u := 10) (t := 13)
    (D := 32) (ψ := (289225193571/10000000000000 : ℝ)) half_17_12_φ5
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, half_17_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, half_17_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, half_17_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_11_12 half_13_12
    (by simpa only [half_17_12_φ6, show (2:ℝ)*32=64 by norm_num] using half_17_12_hx6)
  exact h.weaken (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, half_17_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_12_hx4 : SourcePowerBound (powerBoxCross 18 13 16 half_17_12_φ4) (14742327034131/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 4) (s := 13) (u := 11) (t := 14)
    (D := 16) (ψ := (180675473283/5000000000000 : ℝ)) half_17_12_φ4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, half_17_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, half_17_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, half_17_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_12_12 half_14_12
    (by simpa only [half_17_12_φ5, show (2:ℝ)*16=32 by norm_num] using half_17_12_hx5)
  exact h.weaken (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, half_17_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_12_hx3 : SourcePowerBound (powerBoxCross 18 14 8 half_17_12_φ3) (32528453031497/2000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 3) (s := 14) (u := 12) (t := 15)
    (D := 8) (ψ := (193563389273/5000000000000 : ℝ)) half_17_12_φ3
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, half_17_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, half_17_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, half_17_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_13_12 half_15_12
    (by simpa only [half_17_12_φ4, show (2:ℝ)*8=16 by norm_num] using half_17_12_hx4)
  exact h.weaken (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, half_17_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_12_hx2 : SourcePowerBound (powerBoxCross 18 15 4 half_17_12_φ2) (89851751188919/5000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 2) (s := 15) (u := 13) (t := 16)
    (D := 4) (ψ := (80225681939/2000000000000 : ℝ)) half_17_12_φ2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, half_17_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, half_17_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, half_17_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_14_12 half_16_12
    (by simpa only [half_17_12_φ3, show (2:ℝ)*4=8 by norm_num] using half_17_12_hx3)
  exact h.weaken (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, half_17_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_12_hx1 : SourcePowerBound (powerBoxCross 18 16 2 half_17_12_φ1) (19862934860279/1000000000000 : ℝ) := by
  have h := backward_cross_power (k := 18) (j := 1) (s := 16) (u := 14) (t := 17)
    (D := 2) (ψ := (25751254327/625000000000 : ℝ)) half_17_12_φ1
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, half_17_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, half_17_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])
    (by norm_num) (by norm_num) (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, half_17_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc]) (by norm_num) half_15_12 half_17_11
    (by simpa only [half_17_12_φ2, show (2:ℝ)*2=4 by norm_num] using half_17_12_hx2)
  exact h.weaken (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, half_17_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])

theorem half_17_12 : AdmissibleExponent 18 34 (105854483620411/5000000000000 : ℝ) := by
  have h := first_box_admissible_snoc (k := 18) (s := 15) (ψ := (26370198867/625000000000 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) half_16_12
    (by simpa only [half_17_12_φ1] using half_17_12_hx1)
  exact admissibleExponent_mono h (by norm_num [half_17_12_φ1, half_17_12_φ2, half_17_12_φ3, half_17_12_φ4, half_17_12_φ5, half_17_12_φ6, emptyPhi, total, parameterExponent, curveLoss, shiftExponents, Fin.sum_univ_castSucc, Fin.forall_fin_succ, Fin.snoc])


end Waring.SeedCompletionHigher18SimpleSeeds
