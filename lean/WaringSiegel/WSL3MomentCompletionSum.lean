import WaringSiegel.WSL3MomentCompletionHolder

/-!
# Completing actual finite sums and all their integer moments

The translated-weight formula is passed through a finite exponential sum,
and the exact L1 Fourier mass cost is proved uniformly in translations.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate Classical NumberField SchwartzMap
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

namespace WaringSiegel.WSL3
open WSL2

variable {K : Type*} [Field K] [NumberField K]
variable {α : Type*} [Fintype α]

theorem archimedeanTraceCharacter_frequency_continuous (x : mixedSpace K) :
    Continuous (fun β : mixedSpace K => archimedeanTraceCharacter β x) := by
  have he : (fun β : mixedSpace K => archimedeanTraceCharacter β x) =
      archimedeanTraceCharacter x := by
    funext β
    simp only [archimedeanTraceCharacter, mul_comm β x]
  rw [he]
  exact archimedeanTraceCharacter_continuous x

def completedFiniteSum (points : α → mixedSpace K) (a : α → ℂ) (P : ℝ)
    (β : mixedSpace K) : ℂ :=
  ∑ x, a x * archimedeanTraceCharacter (P⁻¹ • β) (points x)

theorem completedFiniteSum_continuous (points : α → mixedSpace K) (a : α → ℂ) (P : ℝ) :
    Continuous (completedFiniteSum points a P) := by
  apply continuous_finset_sum
  intro x hx
  exact continuous_const.mul ((archimedeanTraceCharacter_frequency_continuous _).comp
    (continuous_const_smul P⁻¹))

theorem completedFiniteSum_norm_le (points : α → mixedSpace K) (a : α → ℂ) (P : ℝ)
    (β : mixedSpace K) : ‖completedFiniteSum points a P β‖ ≤ ∑ x, ‖a x‖ := by
  exact (norm_sum_le _ _).trans_eq (by
    simp only [norm_mul, archimedeanTraceCharacter_norm, mul_one])

theorem finite_sum_shifted_weight_completion (f : 𝓢(mixedSpace K, ℂ))
    (points : α → mixedSpace K) (a : α → ℂ) (P : ℝ) (z : mixedSpace K) :
    (∑ x, a x * f (P⁻¹ • (points x-z))) =
      ∫ β, weightCompletionAmplitude f β *
        (conj (archimedeanTraceCharacter (P⁻¹ • β) z) * completedFiniteSum points a P β) := by
  calc
    _ = ∑ x, ∫ β, a x * (weightCompletionAmplitude f β *
        archimedeanTraceCharacter (P⁻¹ • β) (points x) *
        conj (archimedeanTraceCharacter (P⁻¹ • β) z)) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [integral_const_mul, shifted_weight_completion]
    _ = ∫ β, ∑ x, a x * (weightCompletionAmplitude f β *
        archimedeanTraceCharacter (P⁻¹ • β) (points x) *
        conj (archimedeanTraceCharacter (P⁻¹ • β) z)) :=
      (integral_finset_sum _ (fun x hx =>
        (shifted_weight_completion_integrable f P (points x) z).const_mul (a x))).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with β
      simp only [completedFiniteSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring

theorem completionAmplitude_mul_bounded_pow_integrable (f : 𝓢(mixedSpace K, ℂ))
    (g : mixedSpace K → ℂ) (hg : Continuous g) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ β, ‖g β‖ ≤ M) (n : ℕ) :
    Integrable (fun β => ‖weightCompletionAmplitude f β‖*‖g β‖^n) := by
  apply ((weightCompletionAmplitude_integrable f).norm.mul_const (M^n)).mono'
  · exact ((weightCompletionAmplitude_continuous f).norm.mul (hg.norm.pow n)).aestronglyMeasurable
  · filter_upwards with β
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hb β) n) (norm_nonneg _)

/-- Uniform completion of every positive integer moment, retaining the
oscillatory sum inside the Fourier integral. -/
theorem finite_sum_shifted_weight_moment_completion (f : 𝓢(mixedSpace K, ℂ))
    (points : α → mixedSpace K) (a : α → ℂ) (P : ℝ) (z : mixedSpace K) (n : ℕ) :
    ‖∑ x, a x * f (P⁻¹ • (points x-z))‖^(n+1) ≤
      (∫ β, ‖weightCompletionAmplitude f β‖)^n *
        ∫ β, ‖weightCompletionAmplitude f β‖*‖completedFiniteSum points a P β‖^(n+1) := by
  let g : mixedSpace K → ℂ := fun β =>
    conj (archimedeanTraceCharacter (P⁻¹ • β) z) * completedFiniteSum points a P β
  have hgc : Continuous g :=
    (((archimedeanTraceCharacter_frequency_continuous z).comp
      (continuous_const_smul P⁻¹)).star).mul (completedFiniteSum_continuous points a P)
  have hgn (β : mixedSpace K) : ‖g β‖ = ‖completedFiniteSum points a P β‖ := by
    simp only [g, norm_mul, Complex.norm_conj, archimedeanTraceCharacter_norm, one_mul]
  have hb (β : mixedSpace K) : ‖g β‖ ≤ ∑ x, ‖a x‖ := by
    rw [hgn]
    exact completedFiniteSum_norm_le points a P β
  have hM : 0 ≤ ∑ x, ‖a x‖ := Finset.sum_nonneg (fun x _ => norm_nonneg _)
  have hi n := completionAmplitude_mul_bounded_pow_integrable f g hgc _ hM hb n
  rw [finite_sum_shifted_weight_completion]
  have h := norm_integral_mul_pow_le n (weightCompletionAmplitude f) g
    (weightCompletionAmplitude_integrable f) (weightCompletionAmplitude_continuous f).measurable
    (by simpa only [pow_one] using hi 1) (hi (n+1))
  simpa only [hgn] using h

#print axioms finite_sum_shifted_weight_moment_completion

end WaringSiegel.WSL3
