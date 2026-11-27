import Mathlib.Analysis.Fourier.Inversion

/-!
# Gaussian regularization without an assumed integrable Fourier transform

The Gaussian-regularized inverse integral at zero converges for every
integrable function continuous at zero. The frequency transform itself is
not assumed integrable. This is the analytic input for the positive Fourier
energy argument in the archimedean density application.
-/
noncomputable section
open MeasureTheory Filter Topology Complex
open scoped FourierTransform RealInnerProductSpace
namespace WaringSiegel.WSL3
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
set_option maxHeartbeats 800000

theorem gaussian_regularized_fourier_limit {f : V → ℂ}
    (hf : Integrable f) (hc : ContinuousAt f 0) :
    Tendsto (fun c : ℝ => ∫ w : V,
      Complex.exp (- (c : ℂ)⁻¹ * ‖w‖^2) * Real.fourierIntegral f w)
      atTop (𝓝 (f 0)) := by
  have h := Real.tendsto_integral_gaussian_smul' hf hc
  apply h.congr'
  filter_upwards [Ioi_mem_atTop (0 : ℝ)] with c hc
  have hc' : 0 < c := hc
  have hci : 0 < ((c : ℂ)⁻¹).re := by
    simpa only [← Complex.ofReal_inv, Complex.ofReal_re] using inv_pos.mpr hc'
  have hflip : (innerₗ V).flip = innerₗ V := by
    ext x y
    exact real_inner_comm x y
  have hJ : Integrable (fun w : V => Complex.exp (- (c : ℂ)⁻¹ * ‖w‖^2)) := by
    simpa using GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
      (b := (c : ℂ)⁻¹) hci 0 (0 : V)
  have hF := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := innerₗ V) Real.continuous_fourierChar continuous_inner hJ hf
  rw [hflip] at hF
  change (∫ ξ, Real.fourierIntegral (fun w : V => Complex.exp (-(c : ℂ)⁻¹*‖w‖^2)) ξ * f ξ) =
    (∫ ξ, Complex.exp (-(c : ℂ)⁻¹*‖ξ‖^2) * Real.fourierIntegral f ξ) at hF
  change (∫ w : V, ((Real.pi * c : ℂ) ^ (Module.finrank ℝ V / 2 : ℂ) *
      Complex.exp (-Real.pi^2*c*‖(0 : V)-w‖^2)) * f w) = _
  rw [← hF]
  apply integral_congr_ae
  filter_upwards with w
  change _ = Real.fourierIntegral (fun w : V => Complex.exp (-(c : ℂ)⁻¹*‖w‖^2)) w * f w
  rw [fourierIntegral_gaussian_innerProductSpace hci]
  simp only [zero_sub, norm_neg, div_inv_eq_mul]
  congr 3
  ring

end WaringSiegel.WSL3
