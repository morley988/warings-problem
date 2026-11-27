import WaringSiegel.WSL2TraceTorus

/-!
# WSL2: literal real-algebra trace and the archimedean characters

The trace is mathlib's algebra trace on the actual real algebra R^r × C^s.
Its restriction to K is proved to be the usual field trace, by comparing
the multiplication matrices in the actual integral bases.
-/

noncomputable section
open scoped NumberField nonZeroDivisors BigOperators Classical
open NumberField NumberField.mixedEmbedding Module

namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

def archimedeanTrace : mixedSpace K →ₗ[ℝ] ℝ := Algebra.trace ℝ (mixedSpace K)

theorem archimedeanTrace_field (a : K) :
    archimedeanTrace (mixedEmbedding K a) = (Algebra.trace ℚ K a : ℝ) := by
  rw [archimedeanTrace, Algebra.trace_eq_matrix_trace (NumberField.mixedEmbedding.latticeBasis K),
    Algebra.trace_eq_matrix_trace (NumberField.integralBasis K)]
  simp only [Matrix.trace, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul,
    NumberField.mixedEmbedding.latticeBasis_apply, ← map_mul,
    NumberField.mixedEmbedding.latticeBasis_repr_apply]

theorem archimedeanTrace_pairing_eq_coordinates (a : 𝓞 K) (x : mixedSpace K) :
    archimedeanTrace (mixedEmbedding K (a : K) * x) =
      ∑ i, (integerCoordinates K a i : ℝ) * archimedeanDualCoordinates x i := by
  let b := archimedeanTraceDualBasis (K := K)
  calc
    _ = archimedeanTrace (mixedEmbedding K (a : K) *
        (∑ i, b.repr x i • b i)) := by rw [b.sum_repr]
    _ = ∑ i, b.repr x i * archimedeanTrace (mixedEmbedding K (a : K) * b i) := by
      simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, smul_eq_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [show b i = mixedEmbedding K (integralTraceDualBasis K i) from
        archimedeanTraceDualBasis_apply i, ← map_mul, archimedeanTrace_field,
        ← integerCoordinates_eq_trace]
      simp only [archimedeanDualCoordinates, ContinuousLinearEquiv.coe_coe,
        Basis.equivFun_apply, Rat.cast_intCast, b, mul_comm]
      rfl

theorem latticeCharacter_archimedeanTorusHom (a : 𝓞 K) (x : mixedSpace K) :
    latticeCharacter (integerCoordinates K a) (archimedeanTorusHom x) =
      Complex.exp (2 * Real.pi * Complex.I *
        (archimedeanTrace (mixedEmbedding K (a : K) * x) : ℂ)) := by
  unfold latticeCharacter archimedeanTorusHom
  simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk, fourier_coe_apply,
    Complex.ofReal_one, div_one]
  rw [← Complex.exp_sum, archimedeanTrace_pairing_eq_coordinates]
  congr 1
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The actual real-algebra trace pairing is integral on the embedded inverse
different, so its exponential descends to the actual quotient torus. -/
theorem archimedeanTrace_integer_on_inverseDifferent (a : 𝓞 K)
    {x : mixedSpace K} (hx : x ∈ archInverseDifferentLattice (K := K)) :
    ∃ n : ℤ, (n : ℝ) = archimedeanTrace (mixedEmbedding K (a : K) * x) := by
  obtain ⟨α, hα, rfl⟩ := (mem_archInverseDifferentLattice x).mp hx
  obtain ⟨n, hn⟩ := (mem_inverseDifferent_iff_trace_integral K α).mp hα a
  refine ⟨n, ?_⟩
  rw [← map_mul, archimedeanTrace_field, ← hn]
  simp only [Rat.cast_intCast]

end WaringSiegel
