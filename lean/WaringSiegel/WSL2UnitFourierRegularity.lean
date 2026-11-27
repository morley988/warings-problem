import WaringSiegel.WSL2UnitTraceNormalization
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-!
# Regularity and genuine decay of the literal archimedean root integral

The trace pairing is proved nondegenerate for the actual mixed algebra.
It therefore identifies the actual frequency space with the continuous dual,
so the ordinary Riemann–Lebesgue theorem applies to the genuine root density.
This gives qualitative decay, without a quantitative oscillatory estimate.
-/
noncomputable section
open MeasureTheory Filter Topology
open scoped NumberField BigOperators Classical
open NumberField NumberField.mixedEmbedding
namespace WaringSiegel.WSL2
variable {K : Type*} [Field K] [NumberField K]
set_option maxHeartbeats 800000
local instance : BorelSpace (mixedSpace K) := inferInstance

/-- Symmetry is literal commutativity of multiplication in the mixed algebra. -/
theorem archimedeanTraceCharacter_symm (β x : mixedSpace K) :
    archimedeanTraceCharacter β x = archimedeanTraceCharacter x β := by
  simp only [archimedeanTraceCharacter, mul_comm β x]

/-- The Fourier integral is bounded by the actual source-box volume. -/
theorem archimedeanRootIntegral_norm_le (k : ℕ) (ρ R : ℝ) (β : mixedSpace K) :
    ‖archimedeanRootIntegral k ρ R β‖ ≤ (volume (rootBox K ρ R)).toReal := by
  letI : IsFiniteMeasure (volume.restrict (rootBox K ρ R)) :=
    isFiniteMeasure_restrict.mpr (rootBox_isCompact (K := K) ρ R).measure_lt_top.ne
  unfold archimedeanRootIntegral
  calc
    _ ≤ ∫ x in rootBox K ρ R, ‖archimedeanTraceCharacter β (x^k)‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by simp [archimedeanTraceCharacter_norm, Measure.real]

/-- Continuity in the actual mixed-space frequency parameter. -/
theorem archimedeanRootIntegral_continuous (k : ℕ) (ρ R : ℝ) :
    Continuous (archimedeanRootIntegral (K := K) k ρ R) := by
  letI : IsFiniteMeasure (volume.restrict (rootBox K ρ R)) :=
    isFiniteMeasure_restrict.mpr (rootBox_isCompact (K := K) ρ R).measure_lt_top.ne
  apply continuous_iff_continuousAt.mpr
  intro β
  apply continuousAt_of_dominated (bound := fun _ => (1 : ℝ))
  · exact Eventually.of_forall fun η =>
      ((archimedeanTraceCharacter_continuous η).comp (continuous_id.pow k)).aestronglyMeasurable
  · exact Eventually.of_forall fun η => Eventually.of_forall fun x => by
      rw [archimedeanTraceCharacter_norm]
  · exact integrable_const 1
  · exact Eventually.of_forall fun x => by
      have hc := (archimedeanTraceCharacter_continuous (x^k)).continuousAt (x := β)
      have he : (fun η : mixedSpace K => archimedeanTraceCharacter η (x^k)) =
          archimedeanTraceCharacter (x^k) :=
        funext (fun η => archimedeanTraceCharacter_symm η (x^k))
      rw [he]
      exact hc

/-- Nondegeneracy is proved from the actual standard-coordinate trace matrix. -/
theorem archimedeanTraceForm_nondegenerate :
    (Algebra.traceForm ℝ (mixedSpace K)).Nondegenerate := by
  apply (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (stdBasis K)).mpr
  rw [← Algebra.traceMatrix_of_basis]
  rw [tracePairingMatrix_det]
  exact pow_ne_zero _ (by norm_num)

/-- The actual trace pairing identifies mixed frequency space with its dual. -/
def archimedeanTraceDual : mixedSpace K ≃L[ℝ] StrongDual ℝ (mixedSpace K) :=
  ((Algebra.traceForm ℝ (mixedSpace K)).toDual archimedeanTraceForm_nondegenerate |>.trans
    LinearMap.toContinuousLinearMap).toContinuousLinearEquiv

theorem archimedeanTraceDual_apply (β x : mixedSpace K) :
    archimedeanTraceDual β x = archimedeanTrace (β*x) := rfl

theorem traceDualFourierChar (β x : mixedSpace K) :
    (Real.fourierChar (-(archimedeanTraceDual (-β)) x) : ℂ) =
      archimedeanTraceCharacter β x := by
  rw [archimedeanTraceDual_apply, neg_mul, (archimedeanTrace (K := K)).map_neg,
    neg_neg, Real.fourierChar_apply]
  unfold archimedeanTraceCharacter
  congr 1
  push_cast
  ring

/-- The actual one-root trace integral tends to zero at infinity. The proof
uses its actual L¹ density and the nondegenerate literal trace pairing. -/
theorem archimedeanRootIntegral_tendsto_zero (k : ℕ) (hk : 0 < k)
    (ρ R : ℝ) (hρ : 0 < ρ) :
    Tendsto (archimedeanRootIntegral (K := K) k ρ R)
      (cocompact (mixedSpace K)) (𝓝 0) := by
  let f : mixedSpace K → ℂ := fun x => (archimedeanWaringDensity k 0 ρ R x).toReal
  let e : mixedSpace K ≃L[ℝ] StrongDual ℝ (mixedSpace K) :=
    (ContinuousLinearEquiv.neg ℝ).trans archimedeanTraceDual
  have h := (tendsto_integral_exp_smul_cocompact f (volume : Measure (mixedSpace K))).comp
    e.toHomeomorph.toCocompactMap.cocompact_tendsto'
  convert h using 1
  funext β
  have hid := archimedeanWaringDensity_fourier k 0 hk ρ R hρ β
  simp only [Nat.zero_add, pow_one] at hid
  rw [← hid]
  apply integral_congr_ae
  filter_upwards with x
  change (archimedeanWaringDensity k 0 ρ R x).toReal • archimedeanTraceCharacter β x =
    Real.fourierChar (-(archimedeanTraceDual (-β)) x) • f x
  rw [Submonoid.smul_def, smul_eq_mul, traceDualFourierChar, Complex.real_smul]
  exact mul_comm _ _

end WaringSiegel.WSL2

#print axioms WaringSiegel.WSL2.archimedeanRootIntegral_norm_le
#print axioms WaringSiegel.WSL2.archimedeanRootIntegral_continuous
#print axioms WaringSiegel.WSL2.archimedeanRootIntegral_tendsto_zero
