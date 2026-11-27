import WaringSiegel.WSL3PoissonScaledSmooth

/-!
# Exact linear Poisson for arbitrary smooth compact amplitudes

This general form permits the actual translated product amplitudes arising
in quadratic and cubic Weyl differencing. No family-uniform estimate is
assumed in this exact identity.
-/

noncomputable section
open MeasureTheory Module NumberField NumberField.mixedEmbedding WaringSiegel.WSL2 WaringSiegel.WSL3
open scoped BigOperators Classical NumberField nonZeroDivisors SchwartzMap ContDiff
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

def compactLinearSchwartz (f : mixedSpace K → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (P : ℝ) (hP : P ≠ 0) (β : mixedSpace K) : 𝓢(mixedSpace K, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearEquiv.smulOfNeZero ℝ (mixedSpace K) P⁻¹ (inv_ne_zero hP)).toContinuousLinearEquiv
    (hc.mul_right.toSchwartzMap (hf.mul (archimedeanTraceCharacter_contDiff (P • β))))

theorem compactLinearSchwartz_apply (f : mixedSpace K → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (P : ℝ) (hP : P ≠ 0) (β x : mixedSpace K) :
    compactLinearSchwartz f hf hc P hP β x = f (P⁻¹ • x) * archimedeanTraceCharacter β x := by
  change f (P⁻¹ • x) * archimedeanTraceCharacter (P • β) (P⁻¹ • x) = _
  rw [traceCharacter_smul_cancel P hP]

theorem traceFourier_compactLinear (f : mixedSpace K → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (P : ℝ) (hP : 0 < P) (β ξ : mixedSpace K) :
    traceFourier (compactLinearSchwartz f hf hc P hP.ne' β) ξ =
      P^(finrank ℚ K) • traceFourier f (P • (ξ-β)) := by
  calc
    _ = ∫ x : mixedSpace K,
        archimedeanTraceCharacter (-(P • (ξ-β))) (P⁻¹ • x) * f (P⁻¹ • x) := by
      apply integral_congr_ae
      filter_upwards with x
      change archimedeanTraceCharacter (-ξ) x * compactLinearSchwartz f hf hc P hP.ne' β x = _
      rw [compactLinearSchwartz_apply, ← smul_neg, traceCharacter_smul_cancel P hP.ne']
      have he : -(ξ-β) = -ξ+β := by abel
      rw [he, traceCharacter_frequency_add]
      ring
    _ = _ := by
      have hs := MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg volume
        (fun x : mixedSpace K => archimedeanTraceCharacter (-(P • (ξ-β))) x * f x) hP.le
      simpa only [NumberField.mixedEmbedding.finrank, traceFourier] using hs

def compactLinearSum (f : mixedSpace K → ℂ) (P : ℝ) (β : mixedSpace K) : ℂ :=
  ∑' a : 𝓞 K, f (P⁻¹ • mixedEmbedding K (a:K)) *
    archimedeanTraceCharacter β (mixedEmbedding K (a:K))

theorem compactLinearSum_summable (f : mixedSpace K → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (P : ℝ) (hP : P ≠ 0) (β : mixedSpace K) :
    Summable (fun a : 𝓞 K => f (P⁻¹ • mixedEmbedding K (a:K)) *
      archimedeanTraceCharacter β (mixedEmbedding K (a:K))) := by
  simpa only [compactLinearSchwartz_apply] using
    schwartz_integerRing_summable (compactLinearSchwartz f hf hc P hP β)

theorem poisson_compact_linear (f : mixedSpace K → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (P : ℝ) (hP : 0 < P) (β : mixedSpace K) :
    compactLinearSum f P β =
      (P^(finrank ℚ K) / basisCovolume (NumberField.mixedEmbedding.latticeBasis K)) •
        (∑' ξ : inverseDifferent K, traceFourier f (P • (mixedEmbedding K (ξ:K)-β))) := by
  have h := poisson_integerRing_schwartz (compactLinearSchwartz f hf hc P hP.ne' β)
  simp_rw [compactLinearSchwartz_apply, traceFourier_compactLinear f hf hc P hP] at h
  rw [tsum_const_smul'', smul_smul] at h
  simpa only [compactLinearSum, div_eq_mul_inv, mul_comm] using h

end WaringSiegel.WSL3Poisson
