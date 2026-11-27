import Waring.SeedCompletionNaturalRecurrence
import Waring.PolicyCompletionMajorPowerRanges
import Waring.SeedCompletionScaleAlgebra

/-! # Power-scale normalization of literal full-box parameter counts -/
noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionNaturalBox
open PolicyCompletionMajorBoxRanges PolicyCompletionMajorPowerRanges
open CartesianProductSampling ProductMultiplicity SmoothMoments SeedCompletionSourceBounds

def parameterExponent {j : ℕ} (k : ℕ) (φ : Fin j → ℝ) : ℝ :=
  (j:ℝ)+(1-(k:ℝ))*total φ

def powerBoxMixed {j : ℕ} (k s : ℕ) (D : ℝ) (φ : Fin j → ℝ) (P R : ℝ) : ℝ :=
  boxMixedMoment k s (D*P) P R (fun i => P^(φ i)) (D*P^(1-total φ))

def powerBoxCross {j : ℕ} (k s : ℕ) (D : ℝ) (φ : Fin j → ℝ) (P R : ℝ) : ℝ :=
  boxCrossMoment k s (D*P) P R (fun i => P^(φ i)) (D*P^(1-total φ))

def powerBoxCard {j : ℕ} (k : ℕ) (D : ℝ) (φ : Fin j → ℝ) (P R : ℝ) : ℝ :=
  ((naturalBoxLabels k (D*P) P R (fun i => P^(φ i))).card:ℝ)

theorem total_cons {j : ℕ} (ψ : ℝ) (φ : Fin j → ℝ) :
    total (Fin.cons ψ φ)=ψ+total φ := by simp [total,Fin.sum_univ_succ]

theorem powerBoxCard_bound {k j : ℕ} {D P R : ℝ} (φ : Fin j → ℝ)
    (hD : 0<D) (hP : 0<P) (hR : 0≤R)
    (hφ : ∀ i,0≤φ i) (hshift : ∀ i,0≤shiftExponents k φ i) :
    powerBoxCard k D φ P R≤D^j*P^(parameterExponent k φ)*R^j := by
  have hH : (tupleProduct (boxHeightBounds k (D*P) (fun i => P^(φ i))):ℝ)≤
      ∏ i,boxHeights k (D*P) (fun i => P^(φ i)) i := by
    simp only [tupleProduct,Nat.cast_prod]
    apply Finset.prod_le_prod (fun _ _ => Nat.cast_nonneg _)
    intro i _
    exact Nat.floor_le (boxHeights_pos k (mul_pos hD hP)
      (fun i => Real.rpow_pos_of_pos hP _) i).le
  have hC := boxCoefficientTuples_card_le P hR (fun i => (Real.rpow_pos_of_pos hP (φ i)).le)
  rw [boxHeightProduct_power k hP D φ hshift] at hH
  rw [power_parameters_product hP φ hφ] at hC
  unfold powerBoxCard naturalBoxLabels
  rw [Finset.card_product,Nat.cast_mul,positiveBox_card]
  apply (mul_le_mul hH hC (by positivity) (by positivity)).trans_eq
  calc
    _ = D^j*(P^((j:ℝ)-(k:ℝ)*total φ)*P^(total φ))*R^j := by ring
    _ = _ := by rw [← Real.rpow_add hP]; congr 2; unfold parameterExponent; ring

theorem powerBoxCard_power {k j : ℕ} {D : ℝ} (hD : 1≤D) (φ : Fin j → ℝ)
    (hφ : ∀ i,0≤φ i) (hshift : ∀ i,0≤shiftExponents k φ i) :
    SourcePowerBound (powerBoxCard k D φ) (parameterExponent k φ) := by
  have H := ((constant (D^j)).mul (ambient_power (parameterExponent k φ))).mul
    (smoothness_power.natPow j)
  norm_num only [zero_add,zero_mul,add_zero] at H
  apply H.of_le (fun P R _ _ => by unfold powerBoxCard; positivity)
  intro P R hP hR
  exact powerBoxCard_bound φ (zero_lt_one.trans_le hD) (zero_lt_one.trans_le hP)
    (zero_le_one.trans hR) hφ hshift

theorem naturalCenters_card_bound {L : ℝ} (hL : 0≤L) :
    ((naturalCenters L).card:ℝ)≤L := by
  have heq : (naturalCenters L).card=⌊L⌋₊ := by
    simp [naturalCenters,Int.card_Icc]
  rw [heq]
  exact Nat.floor_le hL

theorem powerCentersCard_power {D : ℝ} (hD : 1≤D) :
    SourcePowerBound (fun P _ => ((naturalCenters (D*P)).card:ℝ)) 1 := by
  have H := (constant D).mul (ambient_power 1)
  norm_num only [zero_add,Real.rpow_one] at H
  apply H.of_le (fun P R _ _ => by positivity)
  intro P R hP hR
  exact naturalCenters_card_bound (mul_nonneg (zero_le_one.trans hD) (zero_le_one.trans hP))

theorem fixed_dilation_lower_smoothness {D P η : ℝ} (hD : 1≤D) (hDP : D≤P)
    (hη : 0<η) : (D*P)^(η/2)≤P^η := by
  have hP : 1≤P := hD.trans hDP
  have H : D*P≤P^2 := by nlinarith
  calc
    _ ≤ (P^2)^(η/2) := Real.rpow_le_rpow (by positivity) H (by positivity)
    _ = P^((2:ℝ)*(η/2)) := by rw [← Real.rpow_natCast_mul (zero_le_one.trans hP)]; norm_num
    _ = _ := by congr 1; ring

#print axioms powerBoxCard_power
#print axioms powerCentersCard_power
end Waring.SeedCompletionNaturalBox
