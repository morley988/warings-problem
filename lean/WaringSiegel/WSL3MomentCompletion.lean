import WaringSiegel.WSL3PoissonTraceSchwartz
import WaringSiegel.WSL3UnitTraceInversion

/-!
# Exact Fourier completion of shifted smooth weights

The amplitude includes the literal factor 4^r₂ required by standard
mixed-space volume. Its L¹ mass is finite and independent of all scales,
translations, and finite node sets.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate Classical NumberField SchwartzMap FourierTransform
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding

namespace WaringSiegel.WSL3
open WSL2 WSL3Poisson

variable {K : Type*} [Field K] [NumberField K]

theorem traceFourier_integrable (f : 𝓢(mixedSpace K, ℂ)) : Integrable (traceFourier f) := by
  have he : traceFourier f = (traceFourierSchwartz f : mixedSpace K → ℂ) :=
    funext (fun β => (traceFourierSchwartz_apply f β).symm)
  rw [he]
  exact (traceFourierSchwartz f).integrable

theorem traceFourier_inversion_schwartz (f : 𝓢(mixedSpace K, ℂ)) (x : mixedSpace K) :
    (∫ β : mixedSpace K, archimedeanTraceCharacter β x * traceFourier f β) =
      ((4 : ℝ)^nrComplexPlaces K)⁻¹ • f x := by
  let F := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (euclidean.toMixed K) f
  let xE := (euclidean.toMixed K).symm x
  have hFT (β : mixedSpace K) : Real.fourierIntegral F (traceFrequency β) =
      traceFourier f β := by
    simpa only [map_neg, neg_neg, traceFourier] using traceFrequency_fourier f (-β)
  have hchar (β : mixedSpace K) : (Real.fourierChar (inner ℝ (traceFrequency β) xE) : ℂ) =
      archimedeanTraceCharacter β x := by
    simpa only [map_neg, neg_neg, xE, ContinuousLinearEquiv.apply_symm_apply] using
      traceFrequency_inverseFourierChar (-β) xE
  calc
    _ = ∫ β : mixedSpace K, Real.fourierChar (inner ℝ (traceFrequency β) xE) •
        Real.fourierIntegral F (traceFrequency β) := by
      apply integral_congr_ae
      filter_upwards with β
      rw [Circle.smul_def, smul_eq_mul, hchar, hFT]
    _ = ((4 : ℝ)^nrComplexPlaces K)⁻¹ •
        Real.fourierIntegralInv (Real.fourierIntegral F) xE := by
      rw [Real.fourierIntegralInv_eq]
      exact traceFrequency_integral_comp
        (fun ξ : euclidean.mixedSpace K => Real.fourierChar (inner ℝ ξ xE) • Real.fourierIntegral F ξ)
    _ = _ := by
      rw [Continuous.fourier_inversion F.continuous F.integrable
        (SchwartzMap.fourierTransformCLM ℂ F).integrable]
      simp only [F, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
        xE, ContinuousLinearEquiv.apply_symm_apply]

def weightCompletionAmplitude (f : 𝓢(mixedSpace K, ℂ)) (β : mixedSpace K) : ℂ :=
  ((4 : ℝ)^nrComplexPlaces K : ℂ) * traceFourier f β

theorem weightCompletionAmplitude_integrable (f : 𝓢(mixedSpace K, ℂ)) :
    Integrable (weightCompletionAmplitude f) :=
  (traceFourier_integrable f).const_mul _

theorem weightCompletionAmplitude_continuous (f : 𝓢(mixedSpace K, ℂ)) :
    Continuous (weightCompletionAmplitude f) := by
  have h : Continuous (traceFourier f) := by
    have he : traceFourier f = (traceFourierSchwartz f : mixedSpace K → ℂ) :=
      funext (fun β => (traceFourierSchwartz_apply f β).symm)
    rw [he]
    exact (traceFourierSchwartz f).continuous
  exact continuous_const.mul h

theorem weight_completion (f : 𝓢(mixedSpace K, ℂ)) (x : mixedSpace K) :
    f x = ∫ β, weightCompletionAmplitude f β * archimedeanTraceCharacter β x := by
  have h := traceFourier_inversion_schwartz f x
  have h4 : ((4 : ℝ)^nrComplexPlaces K : ℂ) ≠ 0 := pow_ne_zero _ (by norm_num)
  calc
    f x = ((4 : ℝ)^nrComplexPlaces K : ℂ) *
        (((4 : ℝ)^nrComplexPlaces K)⁻¹ • f x) := by
      rw [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow]
      field_simp
    _ = ((4 : ℝ)^nrComplexPlaces K : ℂ) *
        (∫ β, archimedeanTraceCharacter β x * traceFourier f β) := by rw [h]
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with β
      dsimp [weightCompletionAmplitude]
      ring

theorem archimedeanTraceCharacter_neg_argument (β x : mixedSpace K) :
    archimedeanTraceCharacter β (-x) = conj (archimedeanTraceCharacter β x) := by
  rw [archimedeanTraceCharacter, archimedeanTraceCharacter, ← Complex.exp_conj]
  congr 1
  simp only [mul_neg, map_neg, Complex.ofReal_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

theorem archimedeanTraceCharacter_sub (β x y : mixedSpace K) :
    archimedeanTraceCharacter β (x-y) =
      archimedeanTraceCharacter β x * conj (archimedeanTraceCharacter β y) := by
  rw [sub_eq_add_neg, archimedeanTraceCharacter_add, archimedeanTraceCharacter_neg_argument]

theorem archimedeanTraceCharacter_smul_argument (β x : mixedSpace K) (c : ℝ) :
    archimedeanTraceCharacter β (c • x) = archimedeanTraceCharacter (c • β) x := by
  simp only [archimedeanTraceCharacter, mul_smul_comm, smul_mul_assoc]

/-- The exact translated and scaled completion used by common translation. -/
theorem shifted_weight_completion (f : 𝓢(mixedSpace K, ℂ)) (P : ℝ) (x z : mixedSpace K) :
    f (P⁻¹ • (x-z)) = ∫ β, weightCompletionAmplitude f β *
      archimedeanTraceCharacter (P⁻¹ • β) x * conj (archimedeanTraceCharacter (P⁻¹ • β) z) := by
  rw [weight_completion f]
  apply integral_congr_ae
  filter_upwards with β
  rw [archimedeanTraceCharacter_smul_argument, archimedeanTraceCharacter_sub, mul_assoc]

/-- Every completed weight has precisely the same integrable majorant. -/
theorem shifted_weight_completion_integrable (f : 𝓢(mixedSpace K, ℂ)) (P : ℝ)
    (x z : mixedSpace K) : Integrable (fun β => weightCompletionAmplitude f β *
      archimedeanTraceCharacter (P⁻¹ • β) x * conj (archimedeanTraceCharacter (P⁻¹ • β) z)) := by
  apply (weightCompletionAmplitude_integrable f).norm.mono'
  · apply Continuous.aestronglyMeasurable
    have hx : Continuous (fun β : mixedSpace K => archimedeanTraceCharacter (P⁻¹ • β) x) := by
      have h : (fun β : mixedSpace K => archimedeanTraceCharacter (P⁻¹ • β) x) =
          (fun β => archimedeanTraceCharacter (P⁻¹ • x) β) := by
        funext β
        simp only [archimedeanTraceCharacter, smul_mul_assoc]
        rw [mul_comm β x]
      rw [h]
      exact archimedeanTraceCharacter_continuous _
    have hz : Continuous (fun β : mixedSpace K => archimedeanTraceCharacter (P⁻¹ • β) z) := by
      have h : (fun β : mixedSpace K => archimedeanTraceCharacter (P⁻¹ • β) z) =
          (fun β => archimedeanTraceCharacter (P⁻¹ • z) β) := by
        funext β
        simp only [archimedeanTraceCharacter, smul_mul_assoc]
        rw [mul_comm β z]
      rw [h]
      exact archimedeanTraceCharacter_continuous _
    exact ((weightCompletionAmplitude_continuous f).mul hx).mul hz.star
  · filter_upwards with β
    simp only [norm_mul, Complex.norm_conj, archimedeanTraceCharacter_norm, mul_one, le_refl]

#print axioms shifted_weight_completion
#print axioms shifted_weight_completion_integrable

end WaringSiegel.WSL3
