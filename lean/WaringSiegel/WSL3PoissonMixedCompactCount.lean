import WaringSiegel.WSL3PoissonMixedWeightedCount
import WaringSiegel.WSL3PoissonMixedComplementS

/-! # The literal smooth mixed aggregate is an actual nonnegative weighted count -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Function Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding WaringSiegel.WSL2
open scoped NumberField Classical BigOperators ContDiff nonZeroDivisors
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

def compactMixedTransformedWeightedCount (u w g v : mixedSpace K → ℂ)
    (huc : HasCompactSupport u) (hwc : HasCompactSupport w)
    (hgc : HasCompactSupport g) (hvc : HasCompactSupport v)
    (H P M R : ℝ) (hH : H ≠ 0) (hP : P ≠ 0) (hM : M ≠ 0) (hR : R ≠ 0) : ℝ :=
  mixedWeightedRealCount
    (fun h : (compactIntegerSupport u huc H hH).erase 0 => (h:𝓞 K))
    (fun z : compactIntegerSupport w hwc P hP => (z:𝓞 K))
    (fun m : compactIntegerSupport g hgc M hM => (m:𝓞 K))
    (fun y : compactIntegerSupport v hvc R hR => (y:𝓞 K))
    (fun h => ‖u (H⁻¹ • mixedEmbedding K ((h:𝓞 K):K))‖)
    (fun z => ‖w (P⁻¹ • mixedEmbedding K ((z:𝓞 K):K))‖)
    (fun m => ‖g (M⁻¹ • mixedEmbedding K ((m:𝓞 K):K))‖)
    (fun y => ‖v (R⁻¹ • mixedEmbedding K ((y:𝓞 K):K))‖)

theorem compactMixedTransformedWeightedCount_nonneg (u w g v : mixedSpace K → ℂ)
    (huc : HasCompactSupport u) (hwc : HasCompactSupport w)
    (hgc : HasCompactSupport g) (hvc : HasCompactSupport v)
    (H P M R : ℝ) (hH : H ≠ 0) (hP : P ≠ 0) (hM : M ≠ 0) (hR : R ≠ 0) :
    0 ≤ compactMixedTransformedWeightedCount u w g v huc hwc hgc hvc H P M R hH hP hM hR :=
  mixedWeightedRealCount_nonneg _ _ _ _ _ _ _ _
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)

/-- The genuine complex aggregate integrates to the actual weighted solution
count. Nonnegativity is established for the integral, not for its integrand. -/
theorem compactMixedSIntegral_eq_weightedCount (u w g v : mixedSpace K → ℂ)
    (huc : HasCompactSupport u) (hwc : HasCompactSupport w)
    (hgc : HasCompactSupport g) (hvc : HasCompactSupport v)
    (H P M R : ℝ) (hH : H ≠ 0) (hP : P ≠ 0) (hM : M ≠ 0) (hR : R ≠ 0)
    (hu : ∀ x, u x = (‖u x‖:ℂ)) (hw : ∀ x, w x = (‖w x‖:ℂ))
    (hg : ∀ x, g x = (‖g x‖:ℂ)) (hv : ∀ x, v x = (‖v x‖:ℂ)) :
    (∫ q, compactMixedSIntegrand u w g v huc hwc hgc hvc H P M R hH hP hM hR q ∂traceHaar) =
      (compactMixedTransformedWeightedCount u w g v huc hwc hgc hvc H P M R hH hP hM hR:ℂ) := by
  unfold compactMixedTransformedWeightedCount
  rw [← mixedWeightedTraceAggregate_integral_real]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro q
  simp only [mixedWeightedTraceAggregate,compactMixedSIntegrand,compactTraceWeylSum,
    ← hu,← hw,← hg,← hv]

theorem compactMixedSIntegral_re_nonneg (u w g v : mixedSpace K → ℂ)
    (huc : HasCompactSupport u) (hwc : HasCompactSupport w)
    (hgc : HasCompactSupport g) (hvc : HasCompactSupport v)
    (H P M R : ℝ) (hH : H ≠ 0) (hP : P ≠ 0) (hM : M ≠ 0) (hR : R ≠ 0)
    (hu : ∀ x, u x = (‖u x‖:ℂ)) (hw : ∀ x, w x = (‖w x‖:ℂ))
    (hg : ∀ x, g x = (‖g x‖:ℂ)) (hv : ∀ x, v x = (‖v x‖:ℂ)) :
    0 ≤ (∫ q, compactMixedSIntegrand u w g v huc hwc hgc hvc H P M R hH hP hM hR q ∂traceHaar).re := by
  rw [compactMixedSIntegral_eq_weightedCount _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hu hw hg hv,Complex.ofReal_re]
  exact compactMixedTransformedWeightedCount_nonneg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

end WaringSiegel.WSL3Poisson
