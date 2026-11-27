import Waring.ProductBoxGaussian

/-! # Gaussian averaging and exact Fourier interchange -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Waring.ProductBox
open EndgameCompletion QuadraticModulation

def centeredAverage {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) (h : Y → ℝ)
    (θ β : ℝ) : ℂ := ∫ y,e (β*(h y-θ)) ∂ν

theorem integrable_gaussianDamping {T : ℝ} (hT : 0<T) : Integrable (gaussianDamping T) := by
  have hi := (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ)<1)).comp_mul_right'
    (inv_ne_zero hT.ne')
  simpa only [gaussianDamping,div_eq_mul_inv,neg_mul,one_mul] using hi

theorem gaussian_average_identity {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] [SecondCountableTopology Y] (ν : Measure Y) [IsFiniteMeasure ν]
    (h : Y → ℝ) (hh : Continuous h) {T : ℝ} (hT : 0<T) (θ : ℝ) :
    (∫ β : ℝ,(gaussianDamping T β : ℂ)*centeredAverage ν h θ β)=
      ∫ y,((T*Real.pi^(1/2 : ℝ)*Real.exp (-Real.pi^2*T^2*(h y-θ)^2) : ℝ) : ℂ) ∂ν := by
  have hdom : Integrable (fun z : ℝ×Y => gaussianDamping T z.1*(1 : ℝ))
      (volume.prod ν) := (integrable_gaussianDamping hT).mul_prod (integrable_const (1 : ℝ))
  have hcont : Continuous (fun z : ℝ×Y => e (z.1*(h z.2-θ))*(gaussianDamping T z.1 : ℂ)) := by
    unfold e gaussianDamping
    fun_prop
  have hi : Integrable (fun z : ℝ×Y => e (z.1*(h z.2-θ))*(gaussianDamping T z.1 : ℂ))
      (volume.prod ν) := by
    apply hdom.mono' hcont.aestronglyMeasurable
    filter_upwards with z
    rw [norm_mul,norm_e,one_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (gaussianDamping_nonneg _ _),mul_one]
  calc
    _ = ∫ β : ℝ,∫ y,e (β*(h y-θ))*(gaussianDamping T β : ℂ) ∂ν := by
      apply integral_congr_ae
      filter_upwards with β
      rw [integral_mul_const]
      exact mul_comm _ _
    _ = ∫ y,(∫ β : ℝ,e (β*(h y-θ))*(gaussianDamping T β : ℂ)) ∂ν :=
      integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with y
      exact integral_scaled_gaussian_phase hT (h y-θ)

#print axioms gaussian_average_identity
end Waring.ProductBox
