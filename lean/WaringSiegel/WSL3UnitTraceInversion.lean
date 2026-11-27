import WaringSiegel.WSL3UnitFrequencyIntegrability

/-!
# Correctly normalized Fourier inversion for the literal trace pairing

The ordinary mixed-space volume is not self-dual for the literal real-algebra
trace: one complex place contributes an absolute determinant of four. This
file proves the exact factor and identifies the actual absolutely convergent
box singular integral with the continuous density of its image measure.
-/
noncomputable section
open MeasureTheory
open scoped NumberField Classical RealInnerProductSpace
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding WaringSiegel.WSL2
namespace WaringSiegel.WSL3
variable {K : Type*} [Field K] [NumberField K]
set_option maxHeartbeats 800000

theorem traceFrequency_integral_comp_neg {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (f : euclidean.mixedSpace K → A) :
    (∫ β : mixedSpace K, f (-traceFrequency β)) =
      ((4 : ℝ) ^ nrComplexPlaces K)⁻¹ • ∫ ξ, f ξ := by
  calc
    _ = ((4 : ℝ) ^ nrComplexPlaces K)⁻¹ • ∫ ξ : euclidean.mixedSpace K, f (-ξ) :=
      traceFrequency_integral_comp (fun ξ => f (-ξ))
    _ = _ := by
      congr 1
      exact (LinearIsometryEquiv.neg ℝ (E := euclidean.mixedSpace K)).measurePreserving.integral_comp
        (LinearIsometryEquiv.neg ℝ (E := euclidean.mixedSpace K)).toHomeomorph.toMeasurableEquiv.measurableEmbedding f

theorem traceFrequency_inverseFourierChar (β : mixedSpace K) (x : euclidean.mixedSpace K) :
    (Real.fourierChar (inner ℝ (-traceFrequency β) x) : ℂ) =
      archimedeanTraceCharacter (-β) (euclidean.toMixed K x) := by
  have h := traceFrequency_fourierChar (-β) x
  simpa only [map_neg, neg_neg, inner_neg_left, real_inner_comm] using h

/-- General trace inversion under its genuine L¹ hypotheses, with the
literal standard-volume normalization. -/
theorem trace_fourier_inversion {f : mixedSpace K → ℂ} (hf : Integrable f)
    (hc : Continuous f)
    (hFT : Integrable (Real.fourierIntegral
      (fun x : euclidean.mixedSpace K => f (euclidean.toMixed K x))))
    (b : mixedSpace K) :
    (∫ β : mixedSpace K, archimedeanTraceCharacter (-β) b *
      Real.fourierIntegral (fun x : euclidean.mixedSpace K => f (euclidean.toMixed K x))
        (-traceFrequency β)) = ((4 : ℝ) ^ nrComplexPlaces K)⁻¹ • f b := by
  let F : euclidean.mixedSpace K → ℂ := fun x => f (euclidean.toMixed K x)
  let x : euclidean.mixedSpace K := (euclidean.toMixed K).symm b
  have hF : Integrable F :=
    (euclidean.volumePreserving_toMixed K).integrable_comp_of_integrable hf
  have hcF : Continuous F := hc.comp (euclidean.toMixed K).continuous
  have hinv := hF.fourier_inversion hFT (hcF.continuousAt (x := x))
  calc
    _ = ∫ β : mixedSpace K,
        Real.fourierChar (inner ℝ (-traceFrequency β) x) •
          Real.fourierIntegral F (-traceFrequency β) := by
      apply integral_congr_ae
      filter_upwards with β
      rw [Circle.smul_def, smul_eq_mul, traceFrequency_inverseFourierChar]
      simp only [x, ContinuousLinearEquiv.apply_symm_apply, F]
    _ = ((4 : ℝ) ^ nrComplexPlaces K)⁻¹ • Real.fourierIntegralInv
        (Real.fourierIntegral F) x := by
      rw [Real.fourierIntegralInv_eq]
      exact traceFrequency_integral_comp_neg
        (fun ξ : euclidean.mixedSpace K =>
          Real.fourierChar (inner ℝ ξ x) • Real.fourierIntegral F ξ)
    _ = _ := by rw [hinv]; simp only [F, x, ContinuousLinearEquiv.apply_symm_apply]

/-- The ordinary-volume oscillatory singular integral for n roots in the
literal source box. The index n is the actual number of summands. -/
def archimedeanBoxSingularIntegral (k n : ℕ) (ρ R : ℝ) (b : mixedSpace K) : ℂ :=
  ∫ β : mixedSpace K, archimedeanTraceCharacter (-β) b * archimedeanRootIntegral k ρ R β ^ n

/-- Fourier integrability of the continuous actual image density is derived
from the one-root L² density and the proven root-integral bounds. -/
theorem continuousArchimedeanDensity_fourier_integrable (k s : ℕ) (hk : 0 < k)
    (ρ R : ℝ) (hρ : 0 < ρ) :
    Integrable (Real.fourierIntegral (fun x : euclidean.mixedSpace K =>
      (continuousArchimedeanDensity k s ρ R (euclidean.toMixed K x) : ℂ))) := by
  let F : euclidean.mixedSpace K → ℂ := fun x =>
    (continuousArchimedeanDensity k s ρ R (euclidean.toMixed K x) : ℂ)
  have hcomp : Integrable (fun β : mixedSpace K => Real.fourierIntegral F (-traceFrequency β)) := by
    have heq : (fun β : mixedSpace K => Real.fourierIntegral F (-traceFrequency β)) =
        (fun β => archimedeanRootIntegral k ρ R β ^ (s+2)) :=
      funext (fun β => continuousArchimedeanDensity_euclidean_fourier k s hk ρ R hρ β)
    rw [heq]
    exact archimedeanRootIntegral_pow_integrable (K := K) k s hk ρ R hρ
  have hn : Integrable (fun ξ : euclidean.mixedSpace K => Real.fourierIntegral F (-ξ)) :=
    (traceFrequency_integrable_comp (fun ξ => Real.fourierIntegral F (-ξ))).mp hcomp
  have hh : Integrable (fun ξ : euclidean.mixedSpace K => Real.fourierIntegral F (-(-ξ))) :=
    (LinearIsometryEquiv.neg ℝ (E := euclidean.mixedSpace K)).measurePreserving.integrable_comp_of_integrable hn
  simpa only [neg_neg] using hh

/-- Exact inversion for the actual continuous box density: with standard
mixed-space volume, the singular integral is 4⁻ʳ² times that density. -/
theorem archimedeanBoxSingularIntegral_eq_density (k s : ℕ) (hk : 0 < k)
    (ρ R : ℝ) (hρ : 0 < ρ) (b : mixedSpace K) :
    archimedeanBoxSingularIntegral k (s+2) ρ R b =
      ((4 : ℝ) ^ nrComplexPlaces K)⁻¹ • (continuousArchimedeanDensity k s ρ R b : ℂ) := by
  have h := trace_fourier_inversion
    (continuousArchimedeanDensity_integrable k s hk ρ R hρ).ofReal
    (Complex.continuous_ofReal.comp (continuousArchimedeanDensity_continuous k s hk ρ R hρ))
    (continuousArchimedeanDensity_fourier_integrable k s hk ρ R hρ) b
  calc
    _ = ∫ β : mixedSpace K, archimedeanTraceCharacter (-β) b *
        Real.fourierIntegral (fun x : euclidean.mixedSpace K =>
          (continuousArchimedeanDensity k s ρ R (euclidean.toMixed K x) : ℂ))
          (-traceFrequency β) := by
      apply integral_congr_ae
      filter_upwards with β
      rw [continuousArchimedeanDensity_euclidean_fourier k s hk ρ R hρ β]
    _ = _ := h

end WaringSiegel.WSL3

#print axioms WaringSiegel.WSL3.archimedeanBoxSingularIntegral_eq_density
