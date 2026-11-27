import WaringSiegel.WSL3PoissonTrace
import WaringSiegel.WSL3UnitSmoothSchwartz

/-!
# Actual polynomial-phase Poisson summation for the fixed smooth weight

The source is the explicitly constructed smooth product weight, with its
literal polynomial trace phase. Every Schwartz hypothesis is proved by the
source construction; Poisson summation is not an assumption.
-/

noncomputable section
open MeasureTheory Module NumberField NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3
open scoped BigOperators Classical NumberField nonZeroDivisors SchwartzMap
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

def smoothPolynomialLinearIntegral (k : ℕ) (ρ R : ℝ) (β ξ : mixedSpace K) : ℂ :=
  ∫ x, smoothRootWeight ρ R x •
    (archimedeanTraceCharacter β (x^k) * archimedeanTraceCharacter (-ξ) x)

theorem smoothPolynomialLinearIntegral_eq_traceFourier (k : ℕ) (ρ R : ℝ)
    (hρ : 0 < ρ) (hR : 0 < R) (β ξ : mixedSpace K) :
    smoothPolynomialLinearIntegral k ρ R β ξ =
      traceFourier (smoothRootPhaseSchwartz k ρ R hρ hR β) ξ := by
  apply integral_congr_ae
  filter_upwards with x
  change _ = archimedeanTraceCharacter (-ξ) x *
    (smoothRootWeight ρ R x • archimedeanTraceCharacter β (x^k))
  rw [mul_smul_comm, mul_comm]

/-- Exact trace-Poisson identity for the actual smooth polynomial exponential sum. -/
theorem poisson_smooth_polynomial (k : ℕ) (ρ R : ℝ) (hρ : 0 < ρ) (hR : 0 < R)
    (β : mixedSpace K) :
    (∑' a : 𝓞 K, smoothRootWeight ρ R (mixedEmbedding K (a:K)) •
      archimedeanTraceCharacter β ((mixedEmbedding K (a:K))^k)) =
      (basisCovolume (NumberField.mixedEmbedding.latticeBasis K))⁻¹ •
        (∑' ξ : inverseDifferent K,
          smoothPolynomialLinearIntegral k ρ R β (mixedEmbedding K (ξ:K))) := by
  simpa only [smoothRootPhaseSchwartz_apply,
    smoothPolynomialLinearIntegral_eq_traceFourier k ρ R hρ hR] using
      poisson_integerRing_schwartz (smoothRootPhaseSchwartz k ρ R hρ hR β)

/-- The zero frequency in the exact Poisson formula is the actual root integral. -/
theorem smoothPolynomialLinearIntegral_zero (k : ℕ) (ρ R : ℝ) (β : mixedSpace K) :
    smoothPolynomialLinearIntegral k ρ R β 0 =
      weightedRootIntegral k (smoothRootWeight ρ R) β := by
  unfold smoothPolynomialLinearIntegral weightedRootIntegral
  apply integral_congr_ae
  filter_upwards with x
  simp [archimedeanTraceCharacter]

end WaringSiegel.WSL3Poisson
