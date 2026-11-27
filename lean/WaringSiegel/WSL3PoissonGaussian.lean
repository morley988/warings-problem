import WaringSiegel.WSL3PoissonDual
import WaringSiegel.WSL2LongThinDualGaussian
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Gaussian Poisson summation for a genuine finite-dimensional lattice

The Gaussian's original and transformed lattice sums are proved absolutely
convergent. Normal convergence is obtained from the actual coordinate-lattice
count, and the Gaussian Fourier integral is evaluated using mathlib's theorem.
-/

noncomputable section
open MeasureTheory Module Topology TopologicalSpace
open scoped BigOperators Classical SchwartzMap FourierTransform RealInnerProductSpace
namespace WaringSiegel.WSL3Poisson
variable {ι : Type*} [Fintype ι]

/-- Polynomial decay is preserved by an invertible real linear substitution. -/
theorem polynomial_bound_comp_equiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : (ι → ℝ) ≃L[ℝ] E) (f : E → ℂ) (k : ℕ) (C : ℝ)
    (hf : ∀ x, (1+‖x‖)^k*‖f x‖ ≤ C) (x : ι → ℝ) :
    (1+‖x‖)^k*‖f (A x)‖ ≤ (1+‖A.symm.toContinuousLinearMap‖)^k*C := by
  have hx : ‖x‖ ≤ ‖A.symm.toContinuousLinearMap‖*‖A x‖ := by
    simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] using
      A.symm.toContinuousLinearMap.le_opNorm (A x)
  have hw : (1+‖x‖)^k ≤
      (1+‖A.symm.toContinuousLinearMap‖)^k*(1+‖A x‖)^k := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have hA := norm_nonneg A.symm.toContinuousLinearMap
    have hy := norm_nonneg (A x)
    nlinarith
  calc
    _ ≤ ((1+‖A.symm.toContinuousLinearMap‖)^k*(1+‖A x‖)^k)*‖f (A x)‖ :=
      mul_le_mul_of_nonneg_right hw (norm_nonneg _)
    _ = (1+‖A.symm.toContinuousLinearMap‖)^k*((1+‖A x‖)^k*‖f (A x)‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hf _) (by positivity)

theorem integer_summable_of_polynomial_bound (f : (ι → ℝ) → ℂ) (C : ℝ)
    (hf : ∀ x, (1+‖x‖)^(Fintype.card ι+2)*‖f x‖ ≤ C) :
    Summable fun n : ι → ℤ => f (intVector n) := by
  apply Summable.of_norm_bounded (integer_radial_decay_summable.1.mul_left C)
  intro n
  rw [mul_one_div, le_div_iff₀ (by positivity)]
  simpa only [mul_comm] using hf (intVector n)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A real positive Gaussian, viewed in the complex Fourier codomain. -/
def gaussian (a : ℝ) (x : E) : ℂ := (Real.exp (-a*‖x‖^2) : ℝ)

theorem gaussian_eq_cexp (a : ℝ) (x : E) :
    gaussian a x = Complex.exp (-(a:ℂ)*(‖x‖:ℂ)^2) := by
  rw [gaussian, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

theorem gaussian_eq_cexp_fun (a : ℝ) :
    (gaussian a : E → ℂ) = fun x => Complex.exp (-(a:ℂ)*(‖x‖:ℂ)^2) :=
  funext (gaussian_eq_cexp a)

theorem gaussian_continuous (a : ℝ) : Continuous (gaussian a : E → ℂ) := by
  unfold gaussian
  fun_prop

theorem gaussian_norm (a : ℝ) (x : E) : ‖gaussian a x‖ = Real.exp (-a*‖x‖^2) := by
  simp only [gaussian, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- The decay used below is proved for all Gaussian parameters at least one. -/
theorem gaussian_polynomial_bound (a : ℝ) (ha : 1 ≤ a) (k : ℕ) (x : E) :
    (1+‖x‖)^k*‖gaussian a x‖ ≤ Real.exp ((k:ℝ)^2/4) := by
  rw [gaussian_norm]
  have hg := WaringSiegel.gaussian_le_polynomial_decay ‖x‖ (norm_nonneg x) k
  have hdec : Real.exp (-a*‖x‖^2) ≤ Real.exp (-‖x‖^2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg ‖x‖]
  have h := hdec.trans hg
  simpa only [mul_comm] using (le_div_iff₀ (by positivity)).mp h

/-- Gaussian integrability is proved directly, independently of lattice summation. -/
theorem gaussian_integrable (a : ℝ) (ha : 0 < a) : Integrable (gaussian a : E → ℂ) := by
  rw [gaussian_eq_cexp_fun]
  convert GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V:=E) (b:=(a:ℂ)) ha 0 (0:E) using 1
  ext x
  simp

/-- With the standard π-normalization, the Gaussian is its own Fourier transform. -/
theorem gaussian_pi_fourier (w : E) :
    𝓕 (gaussian Real.pi : E → ℂ) w = gaussian Real.pi w := by
  rw [gaussian_eq_cexp_fun]
  rw [fourierIntegral_gaussian_innerProductSpace (b:=(Real.pi:ℂ)) Real.pi_pos]
  rw [div_self (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero), Complex.one_cpow, one_mul]
  congr 1
  field_simp

/-- A Gaussian remains absolutely summable after every lattice-coordinate substitution. -/
theorem gaussian_equiv_integer_summable (A : (ι → ℝ) ≃L[ℝ] E)
    (a : ℝ) (ha : 1 ≤ a) :
    Summable fun n : ι → ℤ => gaussian a (A (intVector n)) := by
  apply integer_summable_of_polynomial_bound (ι:=ι) (fun x => gaussian a (A x))
    ((1+‖A.symm.toContinuousLinearMap‖)^(Fintype.card ι+2)*
      Real.exp (((Fintype.card ι+2:ℕ):ℝ)^2/4))
  exact polynomial_bound_comp_equiv A (gaussian a) (Fintype.card ι+2) _
    (gaussian_polynomial_bound a ha (Fintype.card ι+2))

/-- Integrability is preserved by the actual basis coordinate map. -/
theorem basis_integrable_comp (b : Basis ι ℝ E) (f : E → ℂ) :
    Integrable (fun x : ι → ℝ => f (b.equivFunL.symm x)) ↔ Integrable f := by
  have h := integrable_map_equiv (μ:=volume) b.equivFunL.symm.toHomeomorph.toMeasurableEquiv f
  change Integrable f (Measure.map b.equivFunL.symm volume) ↔
    Integrable (fun x : ι → ℝ => f (b.equivFunL.symm x)) at h
  rw [basis_map_volume, integrable_smul_measure
    (ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr (basisCovolume_pos b))) ENNReal.ofReal_ne_top] at h
  exact h.symm

/-- Gaussian Poisson with actual dual lattice, convergent sums, and the actual
volume of the original lattice fundamental domain. -/
theorem poisson_gaussian_basis (b : Basis ι ℝ E) :
    (∑' n : ι → ℤ, gaussian Real.pi (b.equivFunL.symm (intVector n))) =
      (basisCovolume b)⁻¹ •
        (∑' n : ι → ℤ, gaussian Real.pi (basisDualCoordinates b (intVector n))) := by
  have hpi : 1 ≤ Real.pi := by linarith [Real.two_le_pi]
  let f : C((ι → ℝ), ℂ) :=
    ⟨fun x => gaussian Real.pi (b.equivFunL.symm x),
      (gaussian_continuous _).comp b.equivFunL.symm.continuous⟩
  have hf : Integrable f :=
    (basis_integrable_comp b (gaussian Real.pi)).mpr (gaussian_integrable _ Real.pi_pos)
  have hn := locally_normal_of_polynomial_bound f
    ((1+‖b.equivFunL.toContinuousLinearMap‖)^(Fintype.card ι+2)*
      Real.exp (((Fintype.card ι+2:ℕ):ℝ)^2/4)) (by positivity)
    (polynomial_bound_comp_equiv b.equivFunL.symm (gaussian Real.pi) _ _
      (gaussian_polynomial_bound Real.pi hpi (Fintype.card ι+2)))
  have hc (n : ι → ℤ) : integerFourier f n =
      (basisCovolume b)⁻¹ • gaussian Real.pi (basisDualCoordinates b (intVector n)) := by
    change integerFourier (fun x => gaussian Real.pi (b.equivFunL.symm x)) n = _
    rw [integerFourier_basis_comp, basisFourier_eq_euclidean, gaussian_pi_fourier]
  have hF : Summable (integerFourier f) := by
    have h := (gaussian_equiv_integer_summable (basisDualCoordinates b) Real.pi hpi).const_smul
      ((basisCovolume b)⁻¹)
    apply h.congr
    intro n
    exact (hc n).symm
  have h := poisson_integer_lattice_zero f hf hn hF
  simp_rw [hc] at h
  rw [tsum_const_smul''] at h
  exact h

/-- The real-valued Gaussian theta identity, ready for positive-series estimates. -/
theorem poisson_gaussian_basis_real (b : Basis ι ℝ E) :
    (∑' n : ι → ℤ, Real.exp (-Real.pi*‖b.equivFunL.symm (intVector n)‖^2)) =
      (basisCovolume b)⁻¹ *
        (∑' n : ι → ℤ, Real.exp (-Real.pi*‖basisDualCoordinates b (intVector n)‖^2)) := by
  apply Complex.ofReal_injective
  simpa only [gaussian, ← Complex.ofReal_tsum, Complex.ofReal_mul,
    Complex.real_smul, Complex.ofReal_inv] using poisson_gaussian_basis b

end WaringSiegel.WSL3Poisson
