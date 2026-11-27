import WaringSiegel.WSL3PoissonPeriodization

/-!
# Multivariate Poisson summation by actual torus Fourier coefficients

The integral of a periodization is unfolded over the integer fundamental
cube. The Fourier coefficients are computed from the original function,
and the existing multivariate Fourier-series theorem then gives Poisson
summation. Normal convergence, integrability, and transformed summability
are the explicit analytic hypotheses to be discharged in applications.
-/

set_option maxHeartbeats 300000

noncomputable section
open MeasureTheory Topology TopologicalSpace
open scoped BigOperators Classical
namespace WaringSiegel.WSL3Poisson
variable {ι : Type*} [Fintype ι]
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- Unfold the genuine sum over the integer translation lattice. -/
theorem integral_unitCube_periodization {f : (ι → ℝ) → ℂ} (hf : Integrable f) :
    (∫ x in unitCube, realPeriodization f x) = ∫ x, f x := by
  have hnorm : (∑' n : ι → ℤ, ∫⁻ x in unitCube, ‖f (x+intVector n)‖ₑ) ≠ ⊤ := by
    have h := unitCube_fundamental.lintegral_eq_tsum'' (fun x => ‖f x‖ₑ)
    simp only [intVector_vadd, add_comm] at h
    rw [← h]
    exact ne_of_lt hf.2
  simp only [realPeriodization]
  rw [integral_tsum]
  · have h := unitCube_fundamental.integral_eq_tsum'' f hf
    simpa only [intVector_vadd, add_comm] using h.symm
  · intro n
    exact (hf.comp_add_right (intVector n)).aestronglyMeasurable.restrict
  · exact hnorm

/-- Integral transport from normalized Haar measure to the half-open cube. -/
theorem integral_torus_eq_unitCube {g : UnitAddTorus ι → ℂ}
    (hg : AEStronglyMeasurable g latticeHaar) :
    (∫ θ, g θ ∂latticeHaar) = ∫ x in unitCube, g (torusMk x) := by
  have hm := torusMk_measurePreserving (ι := ι)
  have hg' : AEStronglyMeasurable g
      (Measure.map torusMk (volume.restrict (unitCube (ι := ι)))) := by
    rw [hm.map_eq]
    exact hg
  have h := integral_map hm.measurable.aemeasurable hg'
  rw [hm.map_eq] at h
  exact h

/-- The literal continuous integer-frequency character upstairs. -/
def integerCharacter (n : ι → ℤ) (x : ι → ℝ) : ℂ :=
  UnitAddTorus.mFourier n (torusMk x)

theorem integerCharacter_continuous (n : ι → ℤ) : Continuous (integerCharacter n) :=
  (UnitAddTorus.mFourier n).continuous.comp torusMk_isOpenQuotientMap.continuous

theorem integerCharacter_norm (n : ι → ℤ) (x : ι → ℝ) : ‖integerCharacter n x‖ = 1 := by
  simp only [integerCharacter, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
    norm_prod, fourier_apply, Circle.norm_coe, Finset.prod_const_one]

theorem integerCharacter_add_intVector (n m : ι → ℤ) (x : ι → ℝ) :
    integerCharacter n (x+intVector m) = integerCharacter n x := by
  simp only [integerCharacter, torusMk_add_intVector]

/-- Actual Fourier integrals at the integer frequencies. -/
def integerFourier (f : (ι → ℝ) → ℂ) (n : ι → ℤ) : ℂ :=
  ∫ x, integerCharacter (-n) x * f x

theorem integerCharacter_mul_integrable (n : ι → ℤ)
    {f : (ι → ℝ) → ℂ} (hf : Integrable f) :
    Integrable (fun x => integerCharacter n x*f x) := by
  apply hf.norm.mono' ((integerCharacter_continuous n).aestronglyMeasurable.mul hf.1)
  exact Filter.Eventually.of_forall fun x => by
    change ‖integerCharacter n x * f x‖ ≤ ‖f x‖
    rw [norm_mul, integerCharacter_norm, one_mul]

theorem realPeriodization_integerCharacter_mul (n : ι → ℤ)
    (f : (ι → ℝ) → ℂ) (x : ι → ℝ) :
    realPeriodization (fun y => integerCharacter n y*f y) x =
      integerCharacter n x*realPeriodization f x := by
  simp only [realPeriodization, integerCharacter_add_intVector, tsum_mul_left]

/-- Continuous periodization obtained from local normal convergence. -/
def periodizationMap (f : C((ι → ℝ), ℂ))
    (hf : ∀ K : Compacts (ι → ℝ), Summable fun n : ι → ℤ =>
      ‖(f.comp (ContinuousMap.addRight (intVector n))).restrict K‖) : C(UnitAddTorus ι, ℂ) :=
  ⟨torusPeriodization f, torusPeriodization_continuous _ (realPeriodization_continuous_of_normal f hf)⟩

/-- The Fourier coefficient is computed from the original function by the
proved unfolding equality, rather than postulated as an input. -/
theorem periodization_fourierCoeff (f : C((ι → ℝ), ℂ)) (hf : Integrable f)
    (g : C(UnitAddTorus ι, ℂ))
    (hg : ∀ x, g (torusMk x) = realPeriodization f x)
    (n : ι → ℤ) :
    UnitAddTorus.mFourierCoeff g n = integerFourier f n := by
  change (∫ θ, UnitAddTorus.mFourier (-n) θ * g θ ∂latticeHaar) = _
  have htrans := integral_torus_eq_unitCube
    (((UnitAddTorus.mFourier (-n)).continuous.mul g.continuous).aestronglyMeasurable)
  refine htrans.trans ?_
  calc
    (∫ x in unitCube, UnitAddTorus.mFourier (-n) (torusMk x) * g (torusMk x)) =
      ∫ x in unitCube, realPeriodization (fun y => integerCharacter (-n) y * f y) x := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          change integerCharacter (-n) x * g (torusMk x) = _
          rw [hg x]
          exact (realPeriodization_integerCharacter_mul (-n) f x).symm
    _ = integerFourier f n := integral_unitCube_periodization
      (integerCharacter_mul_integrable (-n) hf)

/-- Finite-dimensional Poisson summation on the actual integer lattice. -/
theorem poisson_integer_lattice (f : C((ι → ℝ), ℂ)) (hf : Integrable f)
    (hn : ∀ K : Compacts (ι → ℝ), Summable fun n : ι → ℤ =>
      ‖(f.comp (ContinuousMap.addRight (intVector n))).restrict K‖)
    (hF : Summable (integerFourier f)) (x : ι → ℝ) :
    (∑' n : ι → ℤ, f (x+intVector n)) =
      ∑' n : ι → ℤ, integerFourier f n * integerCharacter n x := by
  let g := periodizationMap f hn
  have hg (x : ι → ℝ) : g (torusMk x) = realPeriodization f x :=
    torusPeriodization_mk f x
  have hc (n : ι → ℤ) : UnitAddTorus.mFourierCoeff g n = integerFourier f n :=
    periodization_fourierCoeff f hf g hg n
  have hfun : UnitAddTorus.mFourierCoeff g = integerFourier f := funext hc
  have hcoeff : Summable (UnitAddTorus.mFourierCoeff g) := by
    rw [hfun]
    exact hF
  have hs := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hcoeff (torusMk x)
  simp only [hc, smul_eq_mul] at hs
  rw [hg] at hs
  exact hs.tsum_eq.symm

theorem poisson_integer_lattice_zero (f : C((ι → ℝ), ℂ)) (hf : Integrable f)
    (hn : ∀ K : Compacts (ι → ℝ), Summable fun n : ι → ℤ =>
      ‖(f.comp (ContinuousMap.addRight (intVector n))).restrict K‖)
    (hF : Summable (integerFourier f)) :
    (∑' n : ι → ℤ, f (intVector n)) = ∑' n : ι → ℤ, integerFourier f n := by
  have h := poisson_integer_lattice f hf hn hF 0
  simpa only [zero_add, integerCharacter, torusMk, Pi.zero_apply,
    AddCircle.coe_zero, UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_eval_zero,
    Finset.prod_const_one, mul_one] using h

end WaringSiegel.WSL3Poisson
