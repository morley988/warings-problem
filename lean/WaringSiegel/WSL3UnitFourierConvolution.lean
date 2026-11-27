import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Convolution

/-!
# Fourier multiplication for genuine integrable convolution

The proof performs the justified Fubini and translation operations for the
literal convolution integral. It will be applied to an actual L²
self-correlation, whose transform is a nonnegative squared modulus.
-/
noncomputable section
open MeasureTheory Filter Topology Complex
open scoped FourierTransform RealInnerProductSpace Convolution
namespace WaringSiegel.WSL3
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
set_option maxHeartbeats 800000

theorem fourier_integrable_convolution {f g : V → ℂ}
    (hf : Integrable f) (hg : Integrable g) (ξ : V) :
    Real.fourierIntegral (fun x : V => ∫ y : V, f y * g (x-y)) ξ =
      Real.fourierIntegral f ξ * Real.fourierIntegral g ξ := by
  let χ : V → ℂ := fun x => Real.fourierChar (-inner ℝ x ξ)
  have hχ : Continuous χ :=
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (continuous_id.inner continuous_const).neg)
  have hi : Integrable (fun p : V × V => χ p.1 * (f p.2 * g (p.1-p.2)))
      (volume.prod volume) := by
    apply (hf.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hg).bdd_mul
      (hχ.comp continuous_fst).aestronglyMeasurable
    refine ⟨1, fun p => ?_⟩
    simp [χ]
  have hs (y : V) : (∫ x : V, χ x * g (x-y)) = χ y * Real.fourierIntegral g ξ := by
    have h := congrFun (VectorFourier.fourierIntegral_comp_add_right
      Real.fourierChar volume (innerₗ V) g (-y)) ξ
    simpa only [VectorFourier.fourierIntegral, Function.comp_apply, ← sub_eq_add_neg,
      LinearMap.neg_apply, innerₗ_apply, inner_neg_left, Real.fourierIntegral, Circle.smul_def, smul_eq_mul, χ] using h
  change (∫ x : V, χ x * ∫ y : V, f y * g (x-y)) = _
  calc
    _ = ∫ x : V, ∫ y : V, χ x * (f y * g (x-y)) := by
      simp_rw [integral_const_mul]
    _ = ∫ y : V, ∫ x : V, χ x * (f y * g (x-y)) := integral_integral_swap hi
    _ = ∫ y : V, f y * (∫ x : V, χ x * g (x-y)) := by
      apply integral_congr_ae
      filter_upwards with y
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      ring
    _ = ∫ y : V, f y * (χ y * Real.fourierIntegral g ξ) := by simp_rw [hs]
    _ = (∫ y : V, χ y * f y) * Real.fourierIntegral g ξ := by
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards with y
      ring
    _ = _ := rfl

end WaringSiegel.WSL3
