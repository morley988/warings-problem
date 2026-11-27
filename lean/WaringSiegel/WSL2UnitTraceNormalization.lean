import WaringSiegel.WSL2UnitFourier
import Mathlib.RingTheory.Complex

/-!
# Literal trace pairing and its standard-coordinate determinant

The mixed space carries standard real/complex Lebesgue volume. Its literal
real-algebra trace pairing has diagonal entries 1 at real coordinates and
2,-2 at the real/imaginary coordinates of every complex place. Thus its
absolute determinant is 4^r₂, and a self-dual volume would have scale 2^r₂.
The determinant statements below are proved for the actual trace matrix.
-/

noncomputable section
open scoped NumberField BigOperators Classical
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
namespace WaringSiegel.WSL2
variable {K : Type*} [Field K] [NumberField K]
set_option maxHeartbeats 800000

/-- The actual real-algebra trace on the mixed archimedean space. -/
theorem archimedeanTrace_eq_sum_real_complex (x : mixedSpace K) :
    archimedeanTrace x = (∑ w, x.1 w) + 2 * (∑ w, (x.2 w).re) := by
  rw [archimedeanTrace, Algebra.trace_eq_matrix_trace (stdBasis K)]
  simp only [Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul,
    Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp [stdBasis, Pi.basis_apply, Pi.basisFun_apply, Pi.mul_apply, Pi.single_apply, Complex.coe_basisOneI,
    Fin.sum_univ_two, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  ring

/-- The trace pairing contains both the complex factor two and the sign
change in imaginary coordinates. -/
theorem archimedeanTrace_pairing_real_coordinates (β x : mixedSpace K) :
    archimedeanTrace (β * x) = (∑ w, β.1 w * x.1 w) +
      ∑ w, (2 * (β.2 w).re * (x.2 w).re - 2 * (β.2 w).im * (x.2 w).im) := by
  rw [archimedeanTrace_eq_sum_real_complex]
  simp only [Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, Complex.mul_re, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro w hw
  ring

def tracePairingDiagonal : index K → ℝ :=
  Sum.elim (fun _ => 1) (fun p => if p.2 = 0 then 2 else -2)

/-- The standard-coordinate matrix is the matrix of the literal algebra
trace form, not a replacement bilinear form. -/
theorem tracePairingMatrix_eq_diagonal :
    Algebra.traceMatrix ℝ (stdBasis K) = Matrix.diagonal (tracePairingDiagonal (K := K)) := by
  ext i j
  change archimedeanTrace ((stdBasis K) i * (stdBasis K) j) = _
  rw [archimedeanTrace_eq_sum_real_complex]
  rcases i with i | ⟨i, p⟩ <;> rcases j with j | ⟨j, q⟩
  · by_cases h : i = j
    · subst j
      simp [stdBasis, Pi.basisFun_apply, Pi.mul_apply, Pi.single_apply, Matrix.diagonal, tracePairingDiagonal, apply_ite]
    · simp [stdBasis, Pi.basisFun_apply, Pi.mul_apply, Pi.single_apply, Matrix.diagonal, tracePairingDiagonal, apply_ite, h, Ne.symm h]
  · simp [stdBasis, Pi.basisFun_apply, Pi.mul_apply, Pi.single_apply, Pi.basis_apply, Matrix.diagonal, tracePairingDiagonal, apply_ite]
  · simp [stdBasis, Pi.basisFun_apply, Pi.mul_apply, Pi.single_apply, Pi.basis_apply, Matrix.diagonal, tracePairingDiagonal, apply_ite]
  · by_cases h : i = j
    · subst j
      fin_cases p <;> fin_cases q <;>
        simp [stdBasis, Pi.basisFun_apply, Pi.mul_apply, Pi.single_apply, Pi.basis_apply, Complex.coe_basisOneI,
          Matrix.diagonal, tracePairingDiagonal, apply_ite]
    · fin_cases p <;> fin_cases q <;>
        simp [stdBasis, Pi.basisFun_apply, Pi.mul_apply, Pi.single_apply, Pi.basis_apply, Complex.coe_basisOneI,
          Matrix.diagonal, tracePairingDiagonal, apply_ite, h, Ne.symm h]

/-- The signed determinant of the actual trace pairing in standard coordinates. -/
theorem tracePairingMatrix_det :
    (Algebra.traceMatrix ℝ (stdBasis K)).det = (-4 : ℝ) ^ nrComplexPlaces K := by
  rw [tracePairingMatrix_eq_diagonal, Matrix.det_diagonal]
  simp [tracePairingDiagonal, Fintype.prod_sum_type, Fintype.prod_prod_type,
    Fin.prod_univ_two, nrComplexPlaces]
  norm_num

/-- Standard-coordinate frequency volume has the factor 4 per complex place. -/
theorem tracePairingMatrix_abs_det :
    |(Algebra.traceMatrix ℝ (stdBasis K)).det| = (4 : ℝ) ^ nrComplexPlaces K := by
  rw [tracePairingMatrix_det, abs_pow]
  norm_num

/-- Change of frequency coordinates for the literal trace matrix. -/
theorem tracePairingMatrix_map_volume :
    MeasureTheory.Measure.map (Matrix.toLin' (Algebra.traceMatrix ℝ (stdBasis K)))
      MeasureTheory.volume =
        ENNReal.ofReal (((4 : ℝ) ^ nrComplexPlaces K)⁻¹) • MeasureTheory.volume := by
  rw [Real.map_matrix_volume_pi_eq_smul_volume_pi]
  · rw [abs_inv, tracePairingMatrix_abs_det]
  · rw [tracePairingMatrix_det]
    exact pow_ne_zero _ (by norm_num)

/-- The self-dual volume scale is the positive square root of that determinant. -/
theorem tracePairingMatrix_sqrt_abs_det :
    Real.sqrt |(Algebra.traceMatrix ℝ (stdBasis K)).det| = (2 : ℝ) ^ nrComplexPlaces K := by
  rw [tracePairingMatrix_abs_det]
  have he : (4 : ℝ) ^ nrComplexPlaces K = ((2 : ℝ) ^ nrComplexPlaces K)^2 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  rw [he, Real.sqrt_sq (by positivity)]

end WaringSiegel.WSL2

#print axioms WaringSiegel.WSL2.tracePairingMatrix_abs_det
#print axioms WaringSiegel.WSL2.tracePairingMatrix_map_volume
