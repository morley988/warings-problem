import WaringSiegel.NumberFieldFourier

/-!
# Integral coordinates as actual number-field trace pairings

The trace-dual basis is constructed from mathlib's nondegenerate trace form,
not supplied as a hypothesis.  Localizing an arbitrary integral basis gives
the coefficient/trace identity, which is then specialized to the exact basis
used by `integerCoordinates` and the Haar coefficient-extraction theorem.
-/

noncomputable section
open scoped NumberField BigOperators nonZeroDivisors

namespace WaringSiegel

variable (K : Type*) [Field K] [NumberField K]

/-- The actual trace-dual basis of a rational basis of a number field. -/
def rationalTraceDualBasis {ι : Type*} [Finite ι] (b : Module.Basis ι ℚ K) :
    Module.Basis ι ℚ K := by
  classical
  exact (Algebra.traceForm ℚ K).dualBasis (traceForm_nondegenerate ℚ K) b

/-- A coordinate functional is multiplication by the corresponding trace-dual vector,
followed by the actual field trace. -/
theorem rational_basis_repr_eq_trace {ι : Type*} [Finite ι]
    (b : Module.Basis ι ℚ K) (x : K) (i : ι) :
    b.repr x i = Algebra.trace ℚ K (x * rationalTraceDualBasis K b i) := by
  classical
  have h := (Algebra.traceForm ℚ K).dualBasis_repr_apply (traceForm_nondegenerate ℚ K)
    (rationalTraceDualBasis K b) x i
  have hdual := LinearMap.BilinForm.dualBasis_dualBasis (Algebra.traceForm ℚ K)
    (traceForm_nondegenerate ℚ K) (Algebra.traceForm_isSymm ℚ) b
  simpa only [rationalTraceDualBasis, hdual, Algebra.traceForm_apply] using h

/-- The trace-dual basis associated to any integral basis of the ring of integers. -/
def integerBasisTraceDual {ι : Type*} [Finite ι] (b : Module.Basis ι ℤ (𝓞 K)) :
    Module.Basis ι ℚ K :=
  rationalTraceDualBasis K (b.localizationLocalization ℚ ℤ⁰ K)

/-- An integral coordinate is exactly an integral trace pairing. -/
theorem integer_basis_repr_eq_trace {ι : Type*} [Finite ι]
    (b : Module.Basis ι ℤ (𝓞 K)) (x : 𝓞 K) (i : ι) :
    (b.repr x i : ℚ) = Algebra.trace ℚ K ((x : K) * integerBasisTraceDual K b i) := by
  have h := rational_basis_repr_eq_trace K
    (b.localizationLocalization ℚ ℤ⁰ K) (x : K) i
  simpa only [Module.Basis.localizationLocalization_repr_algebraMap, map_intCast,
    integerBasisTraceDual] using h

/-- The trace-dual basis for the integral coordinates already used in Fourier extraction. -/
def integralTraceDualBasis : Module.Basis (NumberFieldCoordinateIndex K) ℚ K :=
  integerBasisTraceDual K (NumberField.RingOfIntegers.basis K)

/-- Exact compatibility with the frequency map from `NumberFieldFourier`. -/
theorem integerCoordinates_eq_trace (x : 𝓞 K) (i : NumberFieldCoordinateIndex K) :
    (integerCoordinates K x i : ℚ) =
      Algebra.trace ℚ K ((x : K) * integralTraceDualBasis K i) := by
  simpa only [integerCoordinates, LinearMap.toAddMonoidHom_coe,
    LinearEquiv.coe_coe, Module.Basis.equivFun_apply, integralTraceDualBasis] using
    integer_basis_repr_eq_trace K (NumberField.RingOfIntegers.basis K) x i

/-- A dual-basis coordinate of a field element is its trace against the integral basis. -/
theorem integralTraceDualBasis_repr (α : K) (i : NumberFieldCoordinateIndex K) :
    (integralTraceDualBasis K).repr α i =
      Algebra.trace ℚ K (α * NumberField.integralBasis K i) := by
  classical
  exact (Algebra.traceForm ℚ K).dualBasis_repr_apply (traceForm_nondegenerate ℚ K)
    (NumberField.integralBasis K) α i

/-- The field trace pairing is the dot product of integral and trace-dual coordinates. -/
theorem trace_mul_eq_sum_integerCoordinates (x : 𝓞 K) (α : K) :
    Algebra.trace ℚ K ((x : K) * α) =
      ∑ i, (integerCoordinates K x i : ℚ) * (integralTraceDualBasis K).repr α i := by
  classical
  let b := NumberField.integralBasis K
  calc
    Algebra.trace ℚ K ((x : K) * α) = (Algebra.traceForm ℚ K) (x : K) α := rfl
    _ = (Algebra.traceForm ℚ K) (∑ i, b.repr (x : K) i • b i) α := by rw [b.sum_repr]
    _ = ∑ i, b.repr (x : K) i * Algebra.trace ℚ K (b i * α) := by
      simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
        smul_eq_mul, Algebra.traceForm_apply]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [integralTraceDualBasis_repr]
      simp only [b, NumberField.integralBasis_repr_apply,
        integerCoordinates, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe,
        Module.Basis.equivFun_apply, mul_comm (NumberField.integralBasis K i) α]
      rfl

/-- A field element gives a coordinate-torus point by its trace-dual coordinates. -/
def traceTorusPoint (α : K) : NumberFieldCoordinateIndex K → AddCircle (1 : ℝ) :=
  fun i => (((integralTraceDualBasis K).repr α i : ℝ) : AddCircle (1 : ℝ))

/-- The coordinate character is the literal exponential of the field trace. -/
theorem latticeCharacter_traceTorusPoint (x : 𝓞 K) (α : K) :
    latticeCharacter (integerCoordinates K x) (traceTorusPoint K α) =
      Complex.exp (2 * Real.pi * Complex.I * (Algebra.trace ℚ K ((x : K) * α) : ℂ)) := by
  classical
  unfold latticeCharacter traceTorusPoint
  simp only [fourier_coe_apply, Complex.ofReal_one, div_one, Complex.ofReal_ratCast]
  rw [← Complex.exp_sum]
  congr 1
  rw [trace_mul_eq_sum_integerCoordinates]
  simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end WaringSiegel

#print axioms WaringSiegel.integerCoordinates_eq_trace
#print axioms WaringSiegel.latticeCharacter_traceTorusPoint
