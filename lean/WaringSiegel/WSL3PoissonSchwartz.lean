import WaringSiegel.WSL3PoissonFourier
import WaringSiegel.WSL3PoissonDecay
import Mathlib.Analysis.Distribution.FourierSchwartz

/-!
# Poisson summation for every finite-dimensional Schwartz function

All summability and normal-convergence hypotheses of the preceding torus
argument are discharged here. The Fourier transform is the actual Lebesgue
integral, with the standard minus sign and factor `2π`.
-/

noncomputable section
open MeasureTheory Topology TopologicalSpace
open scoped BigOperators Classical SchwartzMap FourierTransform RealInnerProductSpace
namespace WaringSiegel.WSL3Poisson
variable {ι : Type*} [Fintype ι]
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- The torus character is the literal exponential of the integer dot product. -/
theorem integerCharacter_exp (n : ι → ℤ) (x : ι → ℝ) :
    integerCharacter n x =
      Complex.exp (2*Real.pi*Complex.I * ∑ i, (n i : ℂ)*(x i : ℂ)) := by
  simp only [integerCharacter, UnitAddTorus.mFourier, ContinuousMap.coe_mk,
    torusMk, fourier_coe_apply, Complex.ofReal_one, div_one]
  rw [← Complex.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Standard Euclidean coordinates are measure preserving. -/
theorem euclideanEquiv_measurePreserving :
    MeasurePreserving (EuclideanSpace.equiv ι ℝ) volume volume :=
  EuclideanSpace.volume_preserving_measurableEquiv ι

/-- Integer Fourier coefficients coincide with the actual Euclidean Fourier
integrals under the coordinate equivalence. -/
theorem integerFourier_eq_euclidean (f : (ι → ℝ) → ℂ) (n : ι → ℤ) :
    integerFourier f n =
      𝓕 (fun v : EuclideanSpace ℝ ι => f (EuclideanSpace.equiv ι ℝ v))
        ((EuclideanSpace.equiv ι ℝ).symm (intVector n)) := by
  rw [Real.fourierIntegral_eq']
  rw [← (EuclideanSpace.volume_preserving_measurableEquiv ι).symm.integral_comp
    (EuclideanSpace.measurableEquiv ι).symm.measurableEmbedding]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change integerCharacter (-n) x * f x =
      Complex.exp ((↑(-2*Real.pi*inner ℝ
        ((EuclideanSpace.equiv ι ℝ).symm x)
        ((EuclideanSpace.equiv ι ℝ).symm (intVector n))) * Complex.I)) * f x
    congr 1
    rw [integerCharacter_exp]
    congr 1
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      EuclideanSpace.equiv, PiLp.continuousLinearEquiv_symm_apply, PiLp.toLp_apply,
      intVector, Pi.neg_apply, Int.cast_neg, Complex.ofReal_mul, Complex.ofReal_neg,
      Complex.ofReal_ofNat, Complex.ofReal_sum, Complex.ofReal_intCast]
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring

/-- Fourier samples of a Schwartz function are absolutely summable. -/
theorem schwartz_integerFourier_summable (f : 𝓢((ι → ℝ), ℂ)) :
    Summable (integerFourier f) := by
  let fE : 𝓢(EuclideanSpace ℝ ι, ℂ) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (EuclideanSpace.equiv ι ℝ) f
  let g : 𝓢((ι → ℝ), ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (EuclideanSpace.equiv ι ℝ).symm (SchwartzMap.fourierTransformCLM ℂ fE)
  have h : integerFourier f = fun n : ι → ℤ => g (intVector n) := by
    funext n
    exact integerFourier_eq_euclidean f n
  rw [h]
  exact schwartz_integer_summable g

/-- Poisson summation in arbitrary finite integer-coordinate dimension, with
all analytic convergence requirements proved for Schwartz data. -/
theorem poisson_schwartz (f : 𝓢((ι → ℝ), ℂ)) (x : ι → ℝ) :
    (∑' n : ι → ℤ, f (x+intVector n)) =
      ∑' n : ι → ℤ, integerFourier f n * integerCharacter n x :=
  poisson_integer_lattice f.toContinuousMap f.integrable (schwartz_locally_normal f)
    (schwartz_integerFourier_summable f) x

/-- The zero-shift version used after choosing a lattice basis. -/
theorem poisson_schwartz_zero (f : 𝓢((ι → ℝ), ℂ)) :
    (∑' n : ι → ℤ, f (intVector n)) = ∑' n : ι → ℤ, integerFourier f n :=
  poisson_integer_lattice_zero f.toContinuousMap f.integrable (schwartz_locally_normal f)
    (schwartz_integerFourier_summable f)

end WaringSiegel.WSL3Poisson
