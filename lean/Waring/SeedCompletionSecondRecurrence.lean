import Waring.SeedCompletionSecondScales
import Waring.SeedCompletionFirstMixedRecurrence

/-! # Uniform exponent conversion of the actual second recurrence -/
noncomputable section
namespace Waring.SeedCompletionSecondScales
open SmoothMoments SeedCompletionSourceBounds SeedCompletionInitialMixed
open SeedCompletionFirstMixedRecurrence PolicyCompletionHolder PolicyCompletionFundamental
open SeedCompletionSharpBackward

theorem firstMixed_nonneg (k u : ℕ) (φ₁ P R : ℝ) :
    0 ≤ firstMixed k u φ₁ P R := by
  unfold firstMixed sourceMixedMoment
  rw [mixedFrequencyEvenMoment_eq_card]
  positivity

/-- The exact diagonal and next-stage comparisons. Every moment estimate
in the premises is an already proved admissible exponent or an actual
second cross integral; the recurrence itself has no source assumption. -/
theorem first_mixed_power {k s : ℕ} {φ₁ φ₂ lam χ γ : ℝ}
    (hk : 2 ≤ k)
    (hφ₁ : 0 ≤ φ₁) (hφ₁k : φ₁ ≤ 1/(k : ℝ))
    (hφ₂ : 0 ≤ φ₂) (hφ₂k : φ₂ ≤ 1/(k : ℝ))
    (hU : AdmissibleExponent k (2*(s+1)) lam)
    (hX : SourcePowerBound (secondCross k (s+1) φ₁ φ₂) χ)
    (hdiag : 2+(1-(k : ℝ))*φ₁+φ₂+(1-φ₁-φ₂)*lam ≤ γ)
    (hnext : χ ≤ γ) :
    SourcePowerBound (firstMixed k (s+1) φ₁)
      (1+(1-(k : ℝ))*φ₁+(2*((s : ℝ)+1)-1)*φ₂+γ) := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkp : 0 < (k : ℝ) := by linarith
  have hφ₁mul : φ₁*(k : ℝ) ≤ 1 := (le_div_iff₀ hkp).mp hφ₁k
  have hφ₂mul : φ₂*(k : ℝ) ≤ 1 := (le_div_iff₀ hkp).mp hφ₂k
  have hφ₁half : φ₁ ≤ 1/2 := by nlinarith [mul_nonneg hφ₁ (show 0 ≤ (k : ℝ)-2 by linarith)]
  have hφ₂half : φ₂ ≤ 1/2 := by nlinarith [mul_nonneg hφ₂ (show 0 ≤ (k : ℝ)-2 by linarith)]
  have hq0 : 0 ≤ 1-φ₁-φ₂ := by linarith
  have hq1 : 1-φ₁-φ₂ ≤ 1 := by linarith
  have hA : SourcePowerBound (fun P R : ℝ => P^(1-(k : ℝ)*φ₁)*P^φ₁*R)
      (1+(1-(k : ℝ))*φ₁) := by
    convert (((ambient_power (1-(k : ℝ)*φ₁)).mul (ambient_power φ₁)).mul smoothness_power) using 1 <;> ring
  have hM : SourcePowerBound (fun P R : ℝ => P^φ₂*R) φ₂ := by
    convert (ambient_power φ₂).mul smoothness_power using 1 <;> ring
  have hPscale : SourcePowerBound (fun P _ : ℝ => 2*P) 1 := by
    have H := (constant 2).mul (ambient_power 1)
    simpa only [zero_add,Real.rpow_one] using H
  have hUs := admissible_shorter_source_bound hU (by norm_num : (1 : ℝ) ≤ 2) hq0 hq1
  have hD := (((hA.mul hM).mul hPscale).mul hUs).weaken
    (show (1+(1-(k : ℝ))*φ₁+φ₂)+1+(1-φ₁-φ₂)*lam ≤ γ by linarith)
  have hsum := hD.add (hX.weaken hnext)
  simp only [max_self] at hsum
  have hG := (hA.mul (hM.natPow (2*(s+1)-1))).mul hsum
  have hG' : SourcePowerBound
      (fun P R : ℝ => (P^(1-(k : ℝ)*φ₁)*P^φ₁*R)*(P^φ₂*R)^(2*(s+1)-1)*
        ((P^(1-(k : ℝ)*φ₁)*P^φ₁*R)*(P^φ₂*R)*(2*P)*
          smoothMoment k (2*(s+1)) (2*P^(1-φ₁-φ₂)) R+
          secondCross k (s+1) φ₁ φ₂ P R))
      (1+(1-(k : ℝ))*φ₁+(2*((s : ℝ)+1)-1)*φ₂+γ) := by
    convert hG using 1
    rw [show 2*(s+1)-1=2*s+1 by omega]
    push_cast
    ring
  apply hG'.of_epsilon_domination
  intro δ hδ
  refine ⟨1/4,by norm_num,?_⟩
  intro η hη hηle
  obtain ⟨K,hK,P₀,hP₀,hrec⟩ := first_mixed_recurrence k s hk
    (show 0 < η/2 by positivity) hδ
  refine ⟨K,hK,max P₀ 4,hP₀.trans (le_max_left _ _),?_⟩
  intro P hPP
  have hPP₀ := (le_max_left P₀ 4).trans hPP
  have hP4 : 4 ≤ P := (le_max_right P₀ 4).trans hPP
  have hP : 1 ≤ P := by linarith
  have hPp : 0 < P := by linarith
  have hR : 1 ≤ P^η := Real.one_le_rpow hP hη.le
  have hH : 1 ≤ P^(1-(k : ℝ)*φ₁) := Real.one_le_rpow hP (by nlinarith)
  have hHP : P^(1-(k : ℝ)*φ₁) ≤ 2*P := by
    have H : P^(1-(k : ℝ)*φ₁) ≤ P := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hP
        (show 1-(k : ℝ)*φ₁ ≤ 1 by nlinarith [mul_nonneg hkp.le hφ₁])
    linarith
  have hM₁ := Real.one_le_rpow hP hφ₁
  have hM₂ := Real.one_le_rpow hP hφ₂
  have hM₁R : P^φ₁*P^η ≤ 2*P := by
    rw [← Real.rpow_add hPp]
    have H : P^(φ₁+η) ≤ P := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hP (show φ₁+η ≤ 1 by linarith)
    linarith
  have hM₂Q : P^φ₂ ≤ 2*P^(1-φ₁) := by
    have H := Real.rpow_le_rpow_of_exponent_le hP (show φ₂ ≤ 1-φ₁ by linarith)
    have hpow := Real.rpow_nonneg hPp.le (1-φ₁)
    linarith
  have hQ : 2*P^(1-φ₁) ≤ 4*P := by
    have H : P^(1-φ₁) ≤ P := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hP (show 1-φ₁ ≤ 1 by linarith)
    linarith
  have heq : (2*P^(1-φ₁))/P^φ₂=2*P^(1-φ₁-φ₂) := by
    rw [mul_div_assoc,power_quotient hPp]
  have H := hrec P hPP₀ (P^(1-(k : ℝ)*φ₁)) P (2*P^(1-φ₁)) (P^η) (P^φ₁) (P^φ₂)
    hH hHP hM₁ hM₁R hM₂ hM₂Q hQ (source_lower_smoothness hP4 hη.le)
  rw [heq] at H
  rw [abs_of_nonneg (firstMixed_nonneg ..)]
  have hG0 : 0 ≤ (P^(1-(k : ℝ)*φ₁)*P^φ₁*P^η)*(P^φ₂*P^η)^(2*(s+1)-1)*
      ((P^(1-(k : ℝ)*φ₁)*P^φ₁*P^η)*(P^φ₂*P^η)*(2*P)*
        smoothMoment k (2*(s+1)) (2*P^(1-φ₁-φ₂)) (P^η)+
        secondCross k (s+1) φ₁ φ₂ P (P^η)) := by
    have := smoothMoment_nonneg k (2*(s+1)) (2*P^(1-φ₁-φ₂)) (P^η)
    have := secondCross_nonneg k (s+1) φ₁ φ₂ P (P^η)
    positivity
  rw [abs_of_nonneg hG0]
  simpa only [firstMixed,secondCross,mul_assoc] using H

#print axioms first_mixed_power
end Waring.SeedCompletionSecondScales
