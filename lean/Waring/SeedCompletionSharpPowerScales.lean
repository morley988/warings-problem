import Waring.SeedCompletionDivisorPowerScales

/-! # The sharp residual source normalizer has no curve loss -/
noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionSharpPowerScales
open SeedCompletionTerminalDivisorReal SeedCompletionPaddedSource
open SeedCompletionSourceBounds PolicyCompletionMajorPowerRanges
open PolicyCompletionMajorBoxRanges SeedCompletionNaturalBox
open SeedCompletionDivisorPowerScales

def sharpNormalizer {j : ℕ} (k r : ℕ) (D : ℝ) (φ : Fin j→ℝ) (P R : ℝ) : ℝ :=
  ((D*P)+(∏ i,P^(φ i)*R))*
    ((∏ i,boxHeights k (D*P) (fun i=>P^(φ i)) i)*(D*P)^r*(∏ i,P^(φ i)*R))

theorem sharpNormalizer_nonneg {j : ℕ} (k r : ℕ) {D P R : ℝ} (φ : Fin j→ℝ)
    (hD : 0≤D) (hP : 0<P) (hR : 0≤R) : 0≤sharpNormalizer k r D φ P R := by
  unfold sharpNormalizer boxHeights
  positivity

theorem sharpNormalizer_power {k j : ℕ} (hjk : j<k) (r : ℕ) {D : ℝ} (hD : 1≤D)
    (φ : Fin j→ℝ) (hφ : ∀ i,0≤φ i) (hshift : ∀ i,0≤shiftExponents k φ i) :
    SourcePowerBound (sharpNormalizer k r D φ) (1+parameterExponent k φ+(r:ℝ)) := by
  have hL : SourcePowerBound (fun P _=>D*P) 1 := by
    simpa only [zero_add,Real.rpow_one] using (constant D).mul (ambient_power 1)
  have hM : SourcePowerBound (fun P R=>∏ i,P^(φ i)*R) (total φ) := by
    have H := (ambient_power (total φ)).mul (smoothness_power.natPow j)
    norm_num only [zero_mul,add_zero] at H
    exact H.congr (fun P R hP _=>(coefficient_product_power (zero_lt_one.trans_le hP) φ hφ R).symm)
  have hH : SourcePowerBound
      (fun P _=>∏ i,boxHeights k (D*P) (fun i=>P^(φ i)) i)
      ((j:ℝ)-(k:ℝ)*total φ) := by
    have H := (constant (D^j)).mul (ambient_power ((j:ℝ)-(k:ℝ)*total φ))
    norm_num only [zero_add] at H
    exact H.congr (fun P R hP _=>
      (boxHeightProduct_power k (zero_lt_one.trans_le hP) D φ hshift).symm)
  have H := (hL.add hM).mul ((hH.mul (hL.natPow r)).mul hM)
  have htotal : total φ≤1 := by have h := length_pos hjk φ hshift; linarith
  rw [max_eq_left htotal] at H
  norm_num only [one_mul] at H
  convert H using 1
  unfold parameterExponent
  ring

def sharpDivisorNormalizer {j : ℕ} (k r : ℕ) (D : ℝ) (φ : Fin j→ℝ) (P R : ℝ) : ℝ :=
  swellFactor j R*sharpNormalizer k r D φ P R

theorem sharpDivisorNormalizer_nonneg {j : ℕ} (k r : ℕ) {D P R : ℝ} (φ : Fin j→ℝ)
    (hD : 0≤D) (hP : 0<P) (hR : 0≤R) : 0≤sharpDivisorNormalizer k r D φ P R :=
  mul_nonneg (swellFactor_nonneg j hR) (sharpNormalizer_nonneg k r φ hD hP hR)

theorem sharpDivisorNormalizer_power {k j : ℕ} (hjk : j<k) (r : ℕ) {D : ℝ} (hD : 1≤D)
    (φ : Fin j→ℝ) (hφ : ∀ i,0≤φ i) (hshift : ∀ i,0≤shiftExponents k φ i) :
    SourcePowerBound (sharpDivisorNormalizer k r D φ)
      (1+parameterExponent k φ+(r:ℝ)) := by
  simpa only [zero_add] using (swellFactor_power j).mul
    (sharpNormalizer_power hjk r hD φ hφ hshift)

#print axioms sharpNormalizer_power
#print axioms sharpDivisorNormalizer_power
end Waring.SeedCompletionSharpPowerScales
