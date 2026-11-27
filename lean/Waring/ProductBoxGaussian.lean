import Waring.ProductBoxKernel
import Waring.ProductBoxMeasure
import Mathlib.Analysis.Fourier.Inversion

/-! # Gaussian smoothing of the actual singular integral -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace Waring.ProductBox
open EndgameCompletion QuadraticModulation

def gaussianDamping (T β : ℝ) : ℝ := Real.exp (-(β/T)^2)

theorem gaussianDamping_nonneg (T β : ℝ) : 0≤gaussianDamping T β := (Real.exp_pos _).le

theorem gaussianDamping_le_one (T β : ℝ) : gaussianDamping T β≤1 :=
  Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))

theorem integral_gaussian_phase (h : ℝ) :
    (∫ β : ℝ,e (β*h)*(Real.exp (-β^2) : ℂ))=
      ((Real.pi^(1/2 : ℝ)*Real.exp (-Real.pi^2*h^2) : ℝ) : ℂ) := by
  have hh := fourierIntegral_gaussian (b := (1 : ℂ)) (by norm_num) ((2*Real.pi*h : ℝ) : ℂ)
  have hroot : (Real.pi : ℂ)^(1/2 : ℂ)=((Real.pi^(1/2 : ℝ) : ℝ) : ℂ) := by
    simpa using (Complex.ofReal_cpow Real.pi_pos.le (1/2 : ℝ)).symm
  calc
    _ = ∫ β : ℝ,Complex.exp (Complex.I*((2*Real.pi*h : ℝ) : ℂ)*β)*
        Complex.exp (-(1 : ℂ)*(β : ℂ)^2) := by
      apply integral_congr_ae
      filter_upwards with β
      unfold e
      rw [Complex.ofReal_exp]
      congr 2 <;> push_cast <;> ring
    _ = _ := hh
    _ = _ := by
      rw [div_one,hroot]
      push_cast
      congr 2
      ring

theorem integral_scaled_gaussian_phase {T : ℝ} (hT : 0<T) (h : ℝ) :
    (∫ β : ℝ,e (β*h)*(gaussianDamping T β : ℂ))=
      ((T*Real.pi^(1/2 : ℝ)*Real.exp (-Real.pi^2*T^2*h^2) : ℝ) : ℂ) := by
  have he : (fun β : ℝ => e (β*h)*(gaussianDamping T β : ℂ))=
      (fun β : ℝ => e ((T*(T⁻¹*β))*h)*(Real.exp (-(T⁻¹*β)^2) : ℂ)) := by
    funext β
    rw [mul_inv_cancel_left₀ hT.ne']
    simp only [gaussianDamping,div_eq_mul_inv,mul_comm β]
  rw [he]
  have hscale := Measure.integral_comp_inv_mul_left
    (fun β : ℝ => e ((T*β)*h)*(Real.exp (-β^2) : ℂ)) T
  change (∫ β : ℝ,e ((T*(T⁻¹*β))*h)*(Real.exp (-(T⁻¹*β)^2) : ℂ)) = _ at hscale
  rw [hscale]
  have hs : (fun β : ℝ => e ((T*β)*h)*(Real.exp (-β^2) : ℂ))=
      (fun β : ℝ => e (β*(T*h))*(Real.exp (-β^2) : ℂ)) := by
    funext β
    congr 2
    ring
  rw [hs,integral_gaussian_phase,abs_of_pos hT,Complex.real_smul]
  push_cast
  have hexp : -(Real.pi : ℂ)^2*((T : ℂ)*h)^2=
      -(Real.pi : ℂ)^2*(T : ℂ)^2*(h : ℂ)^2 := by ring
  rw [hexp]
  ring

theorem tendsto_gaussian_damping_integral {F : ℝ → ℂ} (hF : Integrable F) :
    Tendsto (fun T : ℝ => ∫ β : ℝ,(gaussianDamping T β : ℂ)*F β)
      atTop (𝓝 (∫ β : ℝ,F β)) := by
  apply tendsto_integral_filter_of_dominated_convergence _ _ _ hF.norm
  · filter_upwards with β
    have hh : Tendsto (fun T : ℝ => β/T) atTop (𝓝 (0 : ℝ)) := by
      simpa only [div_eq_mul_inv,mul_zero] using
        (tendsto_const_nhds.mul tendsto_inv_atTop_zero :
          Tendsto (fun T : ℝ => β*T⁻¹) atTop (𝓝 (β*0)))
    have hr : Tendsto (fun T : ℝ => Real.exp (-(β/T)^2)) atTop (𝓝 (1 : ℝ)) := by
      have hz : Tendsto (fun T : ℝ => -(β/T)^2) atTop (𝓝 (0 : ℝ)) := by
        simpa using (hh.pow 2).neg
      simpa only [Real.exp_zero] using (Real.continuous_exp.tendsto 0).comp hz
    have hz : Tendsto (fun T : ℝ => (Real.exp (-(β/T)^2) : ℂ)) atTop (𝓝 (1 : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 1).comp hr
    simpa only [gaussianDamping,one_mul] using hz.mul_const (F β)
  · filter_upwards with T
    exact (show Continuous (fun β : ℝ => (gaussianDamping T β : ℂ)) by
      unfold gaussianDamping; fun_prop).aestronglyMeasurable.mul hF.1
  · filter_upwards with T
    filter_upwards with β
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (gaussianDamping_nonneg _ _)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (gaussianDamping_le_one T β) (norm_nonneg _)

#print axioms integral_scaled_gaussian_phase
#print axioms tendsto_gaussian_damping_integral
end Waring.ProductBox
