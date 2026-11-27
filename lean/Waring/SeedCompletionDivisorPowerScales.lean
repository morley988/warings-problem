import Waring.SeedCompletionTerminalDivisorReal
import Waring.SeedCompletionPaddedSecondPower

/-! # Power parameters for the elementary divisor terminal -/
noncomputable section
open scoped BigOperators
namespace Waring.SeedCompletionDivisorPowerScales
open SeedCompletionTerminalDivisorReal SeedCompletionPaddedSource
open SeedCompletionSourceBounds PolicyCompletionMajorPowerRanges
open PolicyCompletionMajorBoxRanges

def phiExtend {j : ℕ} (φ : Fin j→ℝ) (i : ℕ) : ℝ :=
  if h : i<j then φ ⟨i,h⟩ else 0

@[simp] theorem phiExtend_fin {j : ℕ} (φ : Fin j→ℝ) (i : Fin j) :
    phiExtend φ i.val=φ i := by simp [phiExtend,i.isLt]

theorem phiExtend_nonneg {j : ℕ} (φ : Fin j→ℝ) (hφ : ∀ i,0≤φ i) (i : ℕ) :
    0≤phiExtend φ i := by unfold phiExtend; split <;> simp_all

def PrefixCondition {j : ℕ} (k : ℕ) (φ : Fin j→ℝ) : Prop :=
  ∀ i<j,(∑ l ∈ Finset.range i,phiExtend φ l)+((k:ℝ)-1)*phiExtend φ i≤1

theorem power_prefix_condition {k j : ℕ} {D P : ℝ} (hD : 1≤D) (hP : 1≤P)
    (φ : Fin j→ℝ) (hφ : ∀ i,0≤φ i) (hprefix : PrefixCondition k φ) :
    ∀ i<j,(∏ l ∈ Finset.range i,P^(phiExtend φ l))≤
      (D*P^(1-(k:ℝ)*phiExtend φ i))*P^(phiExtend φ i) := by
  intro i hi
  have hPp : 0<P := zero_lt_one.trans_le hP
  calc
    _ = P^(∑ l ∈ Finset.range i,phiExtend φ l) :=
      (Real.rpow_sum_of_nonneg hPp.le (fun l _=>phiExtend_nonneg φ hφ l)).symm
    _ ≤ P^((1-(k:ℝ)*phiExtend φ i)+phiExtend φ i) :=
      Real.rpow_le_rpow_of_exponent_le hP (by have h := hprefix i hi; linarith)
    _ ≤ D*P^((1-(k:ℝ)*phiExtend φ i)+phiExtend φ i) :=
      le_mul_of_one_le_left (Real.rpow_nonneg hPp.le _) hD
    _ = _ := by rw [Real.rpow_add hPp]; ring

theorem swellFactor_power (j : ℕ) : SourcePowerBound (fun _ R=>swellFactor j R) 0 := by
  have H := (constant ((2:ℝ)^j)).mul (((constant 4).mul
    (((constant 2).mul smoothness_power).natPow j)).natPow j)
  norm_num only [zero_add,zero_mul] at H
  exact H

def divisorNormalizer {j : ℕ} (k r : ℕ) (D : ℝ) (φ : Fin j→ℝ) (P R : ℝ) : ℝ :=
  swellFactor j R*paddedNormalizer k r D φ P R

theorem divisorNormalizer_nonneg {j : ℕ} (k r : ℕ) {D P R : ℝ} (φ : Fin j→ℝ)
    (hD : 0≤D) (hP : 0<P) (hR : 0≤R) : 0≤divisorNormalizer k r D φ P R :=
  mul_nonneg (swellFactor_nonneg j hR) (normalizer_nonneg k r φ hD hP hR)

theorem divisorNormalizer_power {k j : ℕ} (r : ℕ) {D : ℝ} (hD : 1≤D)
    (φ : Fin j→ℝ) (hφ : ∀ i,0≤φ i) (hshift : ∀ i,0≤shiftExponents k φ i) :
    SourcePowerBound (divisorNormalizer k r D φ)
      (1+SeedCompletionNaturalBox.parameterExponent k φ+(r:ℝ)+curveLoss φ) := by
  simpa only [zero_add] using (swellFactor_power j).mul
    (paddedNormalizer_power r hD φ hφ hshift)

#print axioms power_prefix_condition
#print axioms divisorNormalizer_power
end Waring.SeedCompletionDivisorPowerScales
