import WaringSiegel.WSL3PoissonBasis
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Actual Euclidean dual lattice and Fourier integrals

Riesz representation of the basis-coordinate functionals constructs the
true dual lattice. No dual-lattice identity is introduced as a hypothesis.
-/

noncomputable section
open MeasureTheory Module Topology
open scoped BigOperators Classical SchwartzMap FourierTransform RealInnerProductSpace
namespace WaringSiegel.WSL3Poisson
variable {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The Riesz realization of the coordinate duality of a real basis. -/
def basisDuality (b : Basis ι ℝ E) : E ≃L[ℝ] E :=
  ((b.toDualEquiv.trans LinearMap.toContinuousLinearMap).trans
    (InnerProductSpace.toDual ℝ E).symm.toLinearEquiv).toContinuousLinearEquiv

theorem basisDuality_inner (b : Basis ι ℝ E) (m x : E) :
    inner ℝ (basisDuality b m) x = b.toDual m x :=
  InnerProductSpace.toDual_symm_apply

/-- Coordinates in the actual Euclidean dual lattice. -/
def basisDualCoordinates (b : Basis ι ℝ E) : (ι → ℝ) ≃L[ℝ] E :=
  b.equivFunL.symm.trans (basisDuality b)

theorem basisDualCoordinates_inner (b : Basis ι ℝ E) (r : ι → ℝ) (x : E) :
    inner ℝ (basisDualCoordinates b r) x = ∑ i, r i * b.equivFunL x i := by
  change inner ℝ (basisDuality b (b.equivFunL.symm r)) x = _
  rw [basisDuality_inner]
  have hx := congrArg (fun y => b.toDual (b.equivFunL.symm r) y) (b.sum_repr x)
  simp only [map_sum, map_smul, smul_eq_mul, Basis.toDual_apply_left] at hx
  rw [← hx]
  have hc (i : ι) : b.repr (b.equivFunL.symm r) i = r i :=
    congrFun (b.equivFun.apply_symm_apply r) i
  apply Finset.sum_congr rfl
  intro i hi
  rw [hc]
  change b.repr x i * r i = r i * b.repr x i
  ring

/-- Coordinate characters are exactly the Fourier phases of the dual lattice. -/
theorem basisFourier_eq_euclidean (b : Basis ι ℝ E) (f : E → ℂ) (n : ι → ℤ) :
    basisFourier b f n = 𝓕 f (basisDualCoordinates b (intVector n)) := by
  rw [Real.fourierIntegral_eq']
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change integerCharacter (-n) (b.equivFunL x)*f x = _
    rw [integerCharacter_exp]
    simp only [smul_eq_mul]
    congr 1
    rw [real_inner_comm, basisDualCoordinates_inner]
    congr 1
    simp only [intVector, Pi.neg_apply, Int.cast_neg, Complex.ofReal_mul,
      Complex.ofReal_neg, Complex.ofReal_ofNat, Complex.ofReal_sum,
      Complex.ofReal_intCast, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring

/-- Standard Euclidean Poisson summation with actual lattice covolume. -/
theorem poisson_euclidean_basis_schwartz (b : Basis ι ℝ E) (f : 𝓢(E, ℂ)) :
    (∑' n : ι → ℤ, f (b.equivFunL.symm (intVector n))) =
      (basisCovolume b)⁻¹ •
        (∑' n : ι → ℤ, 𝓕 f (basisDualCoordinates b (intVector n))) := by
  simpa only [basisFourier_eq_euclidean] using poisson_basis_schwartz b f

/-- The dual coordinates give the integer pairing exactly. -/
theorem basisDualCoordinates_lattice_pairing (b : Basis ι ℝ E) (m n : ι → ℤ) :
    inner ℝ (basisDualCoordinates b (intVector m))
      (b.equivFunL.symm (intVector n)) = ∑ i, (m i : ℝ)*(n i : ℝ) := by
  rw [basisDualCoordinates_inner, ContinuousLinearEquiv.apply_symm_apply]
  rfl

end WaringSiegel.WSL3Poisson
