import WaringSiegel.WSL3PoissonSmooth
import WaringSiegel.WSL3PoissonTraceSchwartz

/-!
# Scaled smooth linear Poisson with exact trace frequencies

The fixed source weight is rescaled by H and modulated by the literal trace
character. The resulting exact formula has the factor H^d/covol(O_K).
-/

noncomputable section
open MeasureTheory Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3
open scoped BigOperators Classical NumberField nonZeroDivisors SchwartzMap
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

def smoothWeightSchwartz (ρ R : ℝ) (hρ : 0 < ρ) (hR : 0 < R) : 𝓢(mixedSpace K, ℂ) :=
  smoothRootPhaseSchwartz 1 ρ R hρ hR 0

theorem smoothWeightSchwartz_apply (ρ R : ℝ) (hρ : 0 < ρ) (hR : 0 < R) (x : mixedSpace K) :
    smoothWeightSchwartz ρ R hρ hR x = (smoothRootWeight ρ R x : ℂ) := by
  simp [smoothWeightSchwartz, smoothRootPhaseSchwartz_apply, archimedeanTraceCharacter,
    Complex.real_smul]

theorem traceCharacter_frequency_add (β γ x : mixedSpace K) :
    archimedeanTraceCharacter (β+γ) x =
      archimedeanTraceCharacter β x * archimedeanTraceCharacter γ x := by
  simp only [archimedeanTraceCharacter, add_mul, map_add, Complex.ofReal_add,
    mul_add, Complex.exp_add]

theorem traceCharacter_smul_cancel (H : ℝ) (hH : H ≠ 0) (β x : mixedSpace K) :
    archimedeanTraceCharacter (H • β) (H⁻¹ • x) = archimedeanTraceCharacter β x := by
  unfold archimedeanTraceCharacter
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, mul_inv_cancel₀ hH, one_smul]

def scaledSmoothLinearSchwartz (ρ R : ℝ) (hρ : 0 < ρ) (hR : 0 < R)
    (H : ℝ) (hH : H ≠ 0) (β : mixedSpace K) : 𝓢(mixedSpace K, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearEquiv.smulOfNeZero ℝ (mixedSpace K) H⁻¹ (inv_ne_zero hH)).toContinuousLinearEquiv
    (smoothRootPhaseSchwartz 1 ρ R hρ hR (H • β))

theorem scaledSmoothLinearSchwartz_apply (ρ R : ℝ) (hρ : 0 < ρ) (hR : 0 < R)
    (H : ℝ) (hH : H ≠ 0) (β x : mixedSpace K) :
    scaledSmoothLinearSchwartz ρ R hρ hR H hH β x =
      smoothRootWeight ρ R (H⁻¹ • x) • archimedeanTraceCharacter β x := by
  change smoothRootWeight ρ R (H⁻¹ • x) •
    archimedeanTraceCharacter (H • β) ((H⁻¹ • x)^1) = _
  rw [pow_one, traceCharacter_smul_cancel H hH]

/-- Actual scaling and modulation of the literal trace Fourier integral. -/
theorem traceFourier_scaledSmoothLinear (ρ R : ℝ) (hρ : 0 < ρ) (hR : 0 < R)
    (H : ℝ) (hH : 0 < H) (β ξ : mixedSpace K) :
    traceFourier (scaledSmoothLinearSchwartz ρ R hρ hR H hH.ne' β) ξ =
      H^(finrank ℚ K) • traceFourier (smoothWeightSchwartz ρ R hρ hR) (H • (ξ-β)) := by
  calc
    _ = ∫ x : mixedSpace K,
        archimedeanTraceCharacter (-(H • (ξ-β))) (H⁻¹ • x) *
          smoothWeightSchwartz ρ R hρ hR (H⁻¹ • x) := by
      apply integral_congr_ae
      filter_upwards with x
      change archimedeanTraceCharacter (-ξ) x *
        scaledSmoothLinearSchwartz ρ R hρ hR H hH.ne' β x = _
      rw [scaledSmoothLinearSchwartz_apply, smoothWeightSchwartz_apply,
        ← smul_neg, traceCharacter_smul_cancel H hH.ne']
      have he : -(ξ-β) = -ξ+β := by abel
      rw [he, traceCharacter_frequency_add, Complex.real_smul]
      ring
    _ = _ := by
      have hs := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg volume
        (fun x : mixedSpace K => archimedeanTraceCharacter (-(H • (ξ-β))) x *
          smoothWeightSchwartz ρ R hρ hR x) hH.le
      simpa only [NumberField.mixedEmbedding.finrank, traceFourier] using hs

/-- The actual scaled, smoothly weighted linear exponential sum. -/
def smoothLinearSum (ρ R H : ℝ) (β : mixedSpace K) : ℂ :=
  ∑' a : 𝓞 K, smoothRootWeight ρ R (H⁻¹ • mixedEmbedding K (a:K)) •
    archimedeanTraceCharacter β (mixedEmbedding K (a:K))

theorem smoothLinearSum_summable (ρ R : ℝ) (hρ : 0 < ρ) (hR : 0 < R)
    (H : ℝ) (hH : H ≠ 0) (β : mixedSpace K) :
    Summable (fun a : 𝓞 K => smoothRootWeight ρ R (H⁻¹ • mixedEmbedding K (a:K)) •
      archimedeanTraceCharacter β (mixedEmbedding K (a:K))) := by
  simpa only [scaledSmoothLinearSchwartz_apply] using
    schwartz_integerRing_summable (scaledSmoothLinearSchwartz ρ R hρ hR H hH β)

/-- Exact scaled linear Poisson, with the actual inverse-different frequencies. -/
theorem poisson_smooth_linear (ρ R : ℝ) (hρ : 0 < ρ) (hR : 0 < R)
    (H : ℝ) (hH : 0 < H) (β : mixedSpace K) :
    smoothLinearSum ρ R H β =
      (H^(finrank ℚ K) / basisCovolume (NumberField.mixedEmbedding.latticeBasis K)) •
        (∑' ξ : inverseDifferent K, traceFourier (smoothWeightSchwartz ρ R hρ hR)
          (H • (mixedEmbedding K (ξ:K)-β))) := by
  have h := poisson_integerRing_schwartz (scaledSmoothLinearSchwartz ρ R hρ hR H hH.ne' β)
  simp_rw [scaledSmoothLinearSchwartz_apply,
    traceFourier_scaledSmoothLinear ρ R hρ hR H hH] at h
  rw [tsum_const_smul'', smul_smul] at h
  simpa only [smoothLinearSum, div_eq_mul_inv, mul_comm] using h

end WaringSiegel.WSL3Poisson
