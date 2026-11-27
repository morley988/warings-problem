import WaringSiegel.WSL3PoissonBasis
import WaringSiegel.WSL2ArchimedeanTrace
import WaringSiegel.WSL2UnitFourier

/-!
# Poisson summation on the actual inverse different with the trace character

The integer indices are replaced by the actual algebraic integer ring and
inverse different using proved lattice-coordinate equivalences. The Fourier
integral uses the literal algebra trace, with the actual covolume factor.
-/

noncomputable section
open MeasureTheory Module NumberField NumberField.mixedEmbedding WaringSiegel.WSL2
open scoped BigOperators Classical NumberField nonZeroDivisors SchwartzMap
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

/-- Integral coordinates as an equivalence, not only an injective map. -/
def integerCoordinatesEquiv (K : Type*) [Field K] [NumberField K] :
    𝓞 K ≃ₗ[ℤ] (NumberFieldCoordinateIndex K → ℤ) :=
  (NumberField.RingOfIntegers.basis K).equivFun

/-- The actual inverse different has precisely the integral trace-dual coordinates. -/
def inverseDifferentCoordinatesEquiv (K : Type*) [Field K] [NumberField K] :
    inverseDifferent K ≃ₗ[ℤ] (NumberFieldCoordinateIndex K → ℤ) :=
  (LinearEquiv.ofEq _ _ (span_integralTraceDualBasis K)).symm.trans
    ((integralTraceDualBasis K).restrictScalars ℤ).equivFun

theorem inverseDifferentCoordinates_cast (a : inverseDifferent K) (i : NumberFieldCoordinateIndex K) :
    ((inverseDifferentCoordinatesEquiv K a i : ℤ) : ℚ) =
      (integralTraceDualBasis K).repr (a:K) i := by
  have h := Basis.restrictScalars_repr_apply ℤ (integralTraceDualBasis K)
    ((LinearEquiv.ofEq _ _ (span_integralTraceDualBasis K)).symm a) i
  exact h

theorem archimedeanDualCoordinates_inverseDifferent (a : inverseDifferent K) :
    archimedeanDualCoordinates (mixedEmbedding K (a:K)) =
      intVector (inverseDifferentCoordinatesEquiv K a) := by
  ext i
  rw [archimedeanDualCoordinates_field]
  change ((integralTraceDualBasis K).repr (a:K) i : ℝ) =
    ((inverseDifferentCoordinatesEquiv K a i : ℤ) : ℝ)
  exact_mod_cast (inverseDifferentCoordinates_cast a i).symm

theorem inverseDifferent_basis_coordinates (a : inverseDifferent K) :
    (archimedeanTraceDualBasis (K:=K)).equivFunL.symm
      (intVector (inverseDifferentCoordinatesEquiv K a)) = mixedEmbedding K (a:K) := by
  apply (archimedeanTraceDualBasis (K:=K)).equivFunL.injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  exact (archimedeanDualCoordinates_inverseDifferent a).symm

theorem integer_basis_coordinates (a : 𝓞 K) :
    (NumberField.mixedEmbedding.latticeBasis K).equivFunL.symm
      (intVector (integerCoordinatesEquiv K a)) = mixedEmbedding K (a:K) := by
  apply (NumberField.mixedEmbedding.latticeBasis K).equivFunL.injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  ext i
  change (integerCoordinatesEquiv K a i : ℝ) =
    (NumberField.mixedEmbedding.latticeBasis K).repr (mixedEmbedding K (a:K)) i
  rw [NumberField.mixedEmbedding.latticeBasis_repr_apply]
  rw [show (a:K) = algebraMap (𝓞 K) K a from rfl,
    NumberField.integralBasis_repr_apply]
  simp only [eq_intCast, Rat.cast_intCast]
  rfl

/-- Fourier integral for the literal negative trace character. -/
def traceFourier (f : mixedSpace K → ℂ) (β : mixedSpace K) : ℂ :=
  ∫ x, archimedeanTraceCharacter (-β) x * f x

theorem inverseDifferent_integer_character (a : 𝓞 K) (x : mixedSpace K) :
    integerCharacter (-(integerCoordinatesEquiv K a)) (archimedeanDualCoordinates x) =
      archimedeanTraceCharacter (-(mixedEmbedding K (a:K))) x := by
  rw [integerCharacter_exp, archimedeanTraceCharacter, neg_mul,
    (archimedeanTrace (K:=K)).map_neg, archimedeanTrace_pairing_eq_coordinates]
  simp only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib,
    Complex.ofReal_neg, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast]
  rfl

theorem inverseDifferent_basisFourier (f : mixedSpace K → ℂ) (a : 𝓞 K) :
    basisFourier (archimedeanTraceDualBasis (K:=K)) f (integerCoordinatesEquiv K a) =
      traceFourier f (mixedEmbedding K (a:K)) := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change integerCharacter (-(integerCoordinatesEquiv K a)) (archimedeanDualCoordinates x)*f x = _
    rw [inverseDifferent_integer_character]

/-- Poisson summation for actual inverse-different points and actual algebraic
integer trace frequencies, normalized by their geometric covolume. -/
theorem poisson_inverseDifferent_schwartz (f : 𝓢(mixedSpace K, ℂ)) :
    (∑' a : inverseDifferent K, f (mixedEmbedding K (a:K))) =
      (basisCovolume (archimedeanTraceDualBasis (K:=K)))⁻¹ •
        (∑' a : 𝓞 K, traceFourier f (mixedEmbedding K (a:K))) := by
  calc
    _ = ∑' n : NumberFieldCoordinateIndex K → ℤ,
        f ((archimedeanTraceDualBasis (K:=K)).equivFunL.symm (intVector n)) := by
      rw [← (inverseDifferentCoordinatesEquiv K).toEquiv.tsum_eq]
      apply tsum_congr
      intro a
      exact congrArg f (inverseDifferent_basis_coordinates a).symm
    _ = _ := by
      rw [poisson_basis_schwartz]
      congr 1
      rw [← (integerCoordinatesEquiv K).toEquiv.tsum_eq]
      apply tsum_congr
      intro a
      exact inverseDifferent_basisFourier f a

/-- Trace pairing against one integral lattice basis vector reads off the
corresponding actual inverse-different coordinate. -/
theorem integral_basis_trace_pairing (i : NumberFieldCoordinateIndex K) (x : mixedSpace K) :
    archimedeanTrace ((NumberField.mixedEmbedding.latticeBasis K i)*x) =
      archimedeanDualCoordinates x i := by
  have h := archimedeanTrace_pairing_eq_coordinates ((NumberField.RingOfIntegers.basis K) i) x
  change archimedeanTrace (mixedEmbedding K (((NumberField.RingOfIntegers.basis K) i):K)*x) =
    ∑ j, (((NumberField.RingOfIntegers.basis K).repr ((NumberField.RingOfIntegers.basis K) i) j : ℤ):ℝ) *
      archimedeanDualCoordinates x j at h
  simpa only [Basis.repr_self, Finsupp.single_apply,
    Int.cast_ite, Int.cast_one, Int.cast_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    NumberField.mixedEmbedding.latticeBasis_apply, NumberField.integralBasis_apply] using h

/-- The literal real trace form is the dot product of the actual two dual bases. -/
theorem trace_pairing_bases (x y : mixedSpace K) :
    archimedeanTrace (x*y) = ∑ i,
      (NumberField.mixedEmbedding.latticeBasis K).equivFunL x i * archimedeanDualCoordinates y i := by
  let b := NumberField.mixedEmbedding.latticeBasis K
  calc
    _ = archimedeanTrace ((∑ i, b.repr x i • b i)*y) := by rw [b.sum_repr]
    _ = ∑ i, b.repr x i * archimedeanTrace (b i*y) := by
      simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, smul_eq_mul]
    _ = _ := by
      simp only [b, integral_basis_trace_pairing]
      rfl

theorem integer_basis_character (a : inverseDifferent K) (x : mixedSpace K) :
    integerCharacter (-(inverseDifferentCoordinatesEquiv K a))
      ((NumberField.mixedEmbedding.latticeBasis K).equivFunL x) =
      archimedeanTraceCharacter (-(mixedEmbedding K (a:K))) x := by
  rw [integerCharacter_exp, archimedeanTraceCharacter, neg_mul,
    (archimedeanTrace (K:=K)).map_neg, mul_comm (mixedEmbedding K (a:K)) x,
    trace_pairing_bases, archimedeanDualCoordinates_inverseDifferent]
  simp only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib,
    Complex.ofReal_neg, Complex.ofReal_sum, Complex.ofReal_mul, intVector,
    Complex.ofReal_intCast]
  congr 2
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem integer_basisFourier (f : mixedSpace K → ℂ) (a : inverseDifferent K) :
    basisFourier (NumberField.mixedEmbedding.latticeBasis K) f (inverseDifferentCoordinatesEquiv K a) =
      traceFourier f (mixedEmbedding K (a:K)) := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change integerCharacter (-(inverseDifferentCoordinatesEquiv K a))
      ((NumberField.mixedEmbedding.latticeBasis K).equivFunL x)*f x = _
    rw [integer_basis_character]

/-- The standard number-field Poisson formula on the actual algebraic integers,
with actual inverse-different trace frequencies and geometric covolume. -/
theorem poisson_integerRing_schwartz (f : 𝓢(mixedSpace K, ℂ)) :
    (∑' a : 𝓞 K, f (mixedEmbedding K (a:K))) =
      (basisCovolume (NumberField.mixedEmbedding.latticeBasis K))⁻¹ •
        (∑' a : inverseDifferent K, traceFourier f (mixedEmbedding K (a:K))) := by
  calc
    _ = ∑' n : NumberFieldCoordinateIndex K → ℤ,
        f ((NumberField.mixedEmbedding.latticeBasis K).equivFunL.symm (intVector n)) := by
      rw [← (integerCoordinatesEquiv K).toEquiv.tsum_eq]
      apply tsum_congr
      intro a
      exact congrArg f (integer_basis_coordinates a).symm
    _ = _ := by
      rw [poisson_basis_schwartz]
      congr 1
      rw [← (inverseDifferentCoordinatesEquiv K).toEquiv.tsum_eq]
      apply tsum_congr
      intro a
      exact integer_basisFourier f a

end WaringSiegel.WSL3Poisson
