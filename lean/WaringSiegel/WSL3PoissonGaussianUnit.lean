import WaringSiegel.WSL3PoissonGaussian

/-!
# Unit-exponent Gaussian Poisson in even dimension

The long-thin lattice lives in twice the field degree. This form keeps its
literal unit-exponent quadratic form and displays the exact power of π.
-/

noncomputable section
open MeasureTheory Module Topology TopologicalSpace
open scoped BigOperators Classical FourierTransform RealInnerProductSpace
namespace WaringSiegel.WSL3Poisson
variable {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Actual Fourier integral of the unit-exponent Gaussian in dimension `2d`. -/
theorem gaussian_one_fourier_even (d : ℕ) (hd : finrank ℝ E = 2*d) (w : E) :
    𝓕 (gaussian 1 : E → ℂ) w =
      (Real.pi^d) • gaussian (Real.pi^2) w := by
  rw [gaussian_eq_cexp_fun]
  simp only [Complex.ofReal_one]
  rw [fourierIntegral_gaussian_innerProductSpace (b:=(1:ℂ)) (by norm_num)]
  simp only [Complex.ofReal_one, div_one]
  rw [hd]
  have he : ((2*d:ℕ):ℂ)/2 = (d:ℂ) := by push_cast; ring
  rw [he, Complex.cpow_natCast]
  rw [gaussian_eq_cexp, Complex.real_smul, Complex.ofReal_pow]
  push_cast
  rfl

/-- Absolute convergence of the real Gaussian lattice sums. -/
theorem gaussian_real_equiv_integer_summable (A : (ι → ℝ) ≃L[ℝ] E)
    (a : ℝ) (ha : 1 ≤ a) :
    Summable fun n : ι → ℤ => Real.exp (-a*‖A (intVector n)‖^2) :=
  Complex.summable_ofReal.mp (gaussian_equiv_integer_summable A a ha)

/-- The actual unit Gaussian theta identity, with every Fourier and convergence
input discharged and its even-dimensional π factor explicit. -/
theorem poisson_gaussian_one_basis (b : Basis ι ℝ E) (d : ℕ)
    (hd : finrank ℝ E = 2*d) :
    (∑' n : ι → ℤ, gaussian 1 (b.equivFunL.symm (intVector n))) =
      ((basisCovolume b)⁻¹ * Real.pi^d) •
        (∑' n : ι → ℤ, gaussian (Real.pi^2) (basisDualCoordinates b (intVector n))) := by
  have hpi : 1 ≤ Real.pi^2 := by nlinarith [Real.two_le_pi]
  let f : C((ι → ℝ), ℂ) :=
    ⟨fun x => gaussian 1 (b.equivFunL.symm x),
      (gaussian_continuous _).comp b.equivFunL.symm.continuous⟩
  have hf : Integrable f :=
    (basis_integrable_comp b (gaussian 1)).mpr (gaussian_integrable _ zero_lt_one)
  have hn := locally_normal_of_polynomial_bound f
    ((1+‖b.equivFunL.toContinuousLinearMap‖)^(Fintype.card ι+2)*
      Real.exp (((Fintype.card ι+2:ℕ):ℝ)^2/4)) (by positivity)
    (polynomial_bound_comp_equiv b.equivFunL.symm (gaussian 1) _ _
      (gaussian_polynomial_bound 1 le_rfl (Fintype.card ι+2)))
  have hc (n : ι → ℤ) : integerFourier f n =
      ((basisCovolume b)⁻¹*Real.pi^d) •
        gaussian (Real.pi^2) (basisDualCoordinates b (intVector n)) := by
    change integerFourier (fun x => gaussian 1 (b.equivFunL.symm x)) n = _
    rw [integerFourier_basis_comp, basisFourier_eq_euclidean,
      gaussian_one_fourier_even d hd, smul_smul]
  have hF : Summable (integerFourier f) := by
    have h := (gaussian_equiv_integer_summable (basisDualCoordinates b) (Real.pi^2) hpi).const_smul
      ((basisCovolume b)⁻¹*Real.pi^d)
    apply h.congr
    intro n
    exact (hc n).symm
  have h := poisson_integer_lattice_zero f hf hn hF
  simp_rw [hc] at h
  rw [tsum_const_smul''] at h
  exact h

theorem poisson_gaussian_one_basis_real (b : Basis ι ℝ E) (d : ℕ)
    (hd : finrank ℝ E = 2*d) :
    (∑' n : ι → ℤ, Real.exp (-‖b.equivFunL.symm (intVector n)‖^2)) =
      ((basisCovolume b)⁻¹ * Real.pi^d) *
        (∑' n : ι → ℤ, Real.exp (-(Real.pi^2)*‖basisDualCoordinates b (intVector n)‖^2)) := by
  apply Complex.ofReal_injective
  simpa only [gaussian, neg_mul, one_mul, ← Complex.ofReal_tsum, Complex.ofReal_mul,
    Complex.real_smul, Complex.ofReal_inv] using poisson_gaussian_one_basis b d hd

end WaringSiegel.WSL3Poisson
