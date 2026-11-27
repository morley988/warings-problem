import WaringSiegel.WSL2UnitFourierRegularity
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The literal trace-frequency change of coordinates

The standard Euclidean mixed space is volume preserving over the ordinary
mixed space. Riesz representation turns the literal algebra trace pairing
into a genuine invertible frequency map. Its determinant is the already
verified determinant of the literal trace matrix, including every complex
factor and sign.
-/
noncomputable section
open MeasureTheory
open scoped NumberField Classical RealInnerProductSpace
open Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding WaringSiegel.WSL2
namespace WaringSiegel.WSL3
variable {K : Type*} [Field K] [NumberField K]
set_option maxHeartbeats 800000

/-- The actual trace frequency represented in the Euclidean mixed space. -/
def traceFrequency : mixedSpace K ≃L[ℝ] euclidean.mixedSpace K :=
  (((Algebra.traceForm ℝ (mixedSpace K)).toDual archimedeanTraceForm_nondegenerate |>.trans
      (euclidean.toMixed K).toLinearEquiv.dualMap).trans
    (LinearMap.toContinuousLinearMap.trans
      (InnerProductSpace.toDual ℝ (euclidean.mixedSpace K)).symm.toLinearEquiv)).toContinuousLinearEquiv

theorem traceFrequency_inner (β : mixedSpace K) (x : euclidean.mixedSpace K) :
    inner ℝ (traceFrequency β) x = archimedeanTrace (β * euclidean.toMixed K x) := by
  exact InnerProductSpace.toDual_symm_apply

/-- The corresponding endomorphism in Euclidean coordinates. -/
def traceFrequencyEnd : euclidean.mixedSpace K ≃L[ℝ] euclidean.mixedSpace K :=
  (euclidean.toMixed K).trans traceFrequency

theorem traceFrequencyEnd_inner (β x : euclidean.mixedSpace K) :
    inner ℝ (traceFrequencyEnd β) x =
      archimedeanTrace (euclidean.toMixed K β * euclidean.toMixed K x) :=
  traceFrequency_inner _ _

theorem toMixed_stdOrthonormalBasis (i : index K) :
    euclidean.toMixed K (euclidean.stdOrthonormalBasis K i) = stdBasis K i := by
  have h := congrArg (fun b : Basis (index K) ℝ (mixedSpace K) => b i)
    (euclidean.stdOrthonormalBasis_map_eq K)
  exact h

/-- The matrix is the actual algebra trace matrix in its standard basis. -/
theorem traceFrequencyEnd_toMatrix :
    LinearMap.toMatrix (euclidean.stdOrthonormalBasis K).toBasis
      (euclidean.stdOrthonormalBasis K).toBasis
      (traceFrequencyEnd (K := K)).toLinearMap = Algebra.traceMatrix ℝ (stdBasis K) := by
  ext i j
  rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, real_inner_comm]
  change inner ℝ (traceFrequencyEnd (euclidean.stdOrthonormalBasis K j))
    (euclidean.stdOrthonormalBasis K i) = _
  rw [traceFrequencyEnd_inner, toMixed_stdOrthonormalBasis, toMixed_stdOrthonormalBasis]
  change archimedeanTrace ((stdBasis K) j * (stdBasis K) i) =
    archimedeanTrace ((stdBasis K) i * (stdBasis K) j)
  rw [mul_comm]

theorem traceFrequencyEnd_det :
    LinearMap.det (traceFrequencyEnd (K := K)).toLinearMap =
      (-4 : ℝ) ^ nrComplexPlaces K := by
  rw [← LinearMap.det_toMatrix (euclidean.stdOrthonormalBasis K).toBasis,
    traceFrequencyEnd_toMatrix, tracePairingMatrix_det]

theorem traceFrequencyEnd_abs_det :
    |LinearMap.det (traceFrequencyEnd (K := K)).toLinearMap| =
      (4 : ℝ) ^ nrComplexPlaces K := by
  rw [traceFrequencyEnd_det, abs_pow]
  norm_num

/-- Frequency volume is scaled by the inverse of 4^r₂. -/
theorem traceFrequencyEnd_map_volume :
    Measure.map (traceFrequencyEnd (K := K)) volume =
      ENNReal.ofReal (((4 : ℝ) ^ nrComplexPlaces K)⁻¹) • volume := by
  have hn : LinearMap.det (traceFrequencyEnd (K := K)).toLinearMap ≠ 0 := by
    rw [traceFrequencyEnd_det]
    exact pow_ne_zero _ (by norm_num)
  rw [show (traceFrequencyEnd (K := K) : euclidean.mixedSpace K → euclidean.mixedSpace K) =
    (traceFrequencyEnd (K := K)).toLinearMap from rfl,
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hn,
    abs_inv, traceFrequencyEnd_abs_det]

theorem traceFrequency_map_volume :
    Measure.map (traceFrequency (K := K)) volume =
      ENNReal.ofReal (((4 : ℝ) ^ nrComplexPlaces K)⁻¹) • volume := by
  rw [← (euclidean.volumePreserving_toMixed K).map_eq,
    Measure.map_map (traceFrequency (K := K)).continuous.measurable
      (euclidean.toMixed K).continuous.measurable]
  exact traceFrequencyEnd_map_volume


/-- Integrability is invariant under the literal, invertible trace-frequency map. -/
theorem traceFrequency_integrable_comp {A : Type*} [NormedAddCommGroup A]
    (f : euclidean.mixedSpace K → A) :
    Integrable (fun β : mixedSpace K => f (traceFrequency β)) ↔ Integrable f := by
  have h := integrable_map_equiv (μ := (volume : Measure (mixedSpace K)))
    (traceFrequency (K := K)).toHomeomorph.toMeasurableEquiv f
  change Integrable f (Measure.map (traceFrequency (K := K)) volume) ↔
    Integrable (fun β : mixedSpace K => f (traceFrequency β)) at h
  rw [traceFrequency_map_volume, integrable_smul_measure (by positivity) ENNReal.ofReal_ne_top] at h
  exact h.symm

/-- Exact normalization of a frequency integral in standard mixed-space volume. -/
theorem traceFrequency_integral_comp {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    (f : euclidean.mixedSpace K → A) :
    (∫ β : mixedSpace K, f (traceFrequency β)) =
      ((4 : ℝ) ^ nrComplexPlaces K)⁻¹ • ∫ ξ, f ξ := by
  have h := integral_map_equiv (μ := (volume : Measure (mixedSpace K)))
    (traceFrequency (K := K)).toHomeomorph.toMeasurableEquiv f
  change (∫ ξ, f ξ ∂Measure.map (traceFrequency (K := K)) volume) =
    (∫ β : mixedSpace K, f (traceFrequency β)) at h
  rw [traceFrequency_map_volume, integral_smul_measure, ENNReal.toReal_ofReal (by positivity)] at h
  exact h.symm

theorem traceFrequency_fourierChar (β : mixedSpace K) (x : euclidean.mixedSpace K) :
    (Real.fourierChar (-inner ℝ x (-traceFrequency β)) : ℂ) =
      archimedeanTraceCharacter β (euclidean.toMixed K x) := by
  rw [inner_neg_right, neg_neg, real_inner_comm, traceFrequency_inner,
    Real.fourierChar_apply]
  unfold archimedeanTraceCharacter
  congr 1
  push_cast
  ring

/-- The ordinary negative-sign Fourier transform equals the positive-sign
literal trace transform at the reflected trace frequency. -/
theorem traceFrequency_fourier (f : mixedSpace K → ℂ) (β : mixedSpace K) :
    Real.fourierIntegral (fun x : euclidean.mixedSpace K => f (euclidean.toMixed K x))
      (-traceFrequency β) = ∫ x, archimedeanTraceCharacter β x * f x := by
  rw [Real.fourierIntegral_eq]
  calc
    _ = ∫ x : euclidean.mixedSpace K,
        archimedeanTraceCharacter β (euclidean.toMixed K x) * f (euclidean.toMixed K x) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [Circle.smul_def, smul_eq_mul, traceFrequency_fourierChar]
    _ = _ := (euclidean.volumePreserving_toMixed K).integral_comp
      (euclidean.toMixed K).toHomeomorph.toMeasurableEquiv.measurableEmbedding
      (fun x : mixedSpace K => archimedeanTraceCharacter β x * f x)

end WaringSiegel.WSL3
