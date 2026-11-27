import WaringSiegel.WSL4MajorFlexibleThreshold

/-! # The optimized rational threshold gives actual integer minor moments -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped BigOperators Classical NumberField SchwartzMap
namespace WaringSiegel.WSL4
open WSL2 WSL3 WSL3Poisson

variable {K : Type*} [Field K] [NumberField K]

theorem compactTraceWeylSum_threshold_shrinking_saving
    (f : 𝓢(mixedSpace K, ℂ)) (hc : HasCompactSupport (f : mixedSpace K → ℂ))
    (k p : ℕ) (hk : 3≤k) (hpT : p≤k*(k+1))
    (hthreshold : Thresholds.threshold k < (p:ℚ)) :
    ∃ a C η : ℝ, 0<a ∧ a<1 ∧ 0<C ∧ 0<η ∧ ∀ (P : ℝ) (hP : 1≤P),
      (∫ q in shrinkingMinorArcs (K := K) k a P,
        ‖compactTraceWeylSum k f hc P (by linarith) q‖^p ∂traceHaar) ≤
        C*(P^finrank ℚ K : ℝ)^((p:ℝ)-k-η) := by
  rcases threshold_improving_witness k p hk hpT hthreshold with
    ⟨r,hr,hrk,hfirst⟩ | ⟨j,hj,hjk,hmT,hsecond⟩
  · exact compactTraceWeylSum_first_threshold_shrinking_saving f hc k r p hk hr hrk hpT hfirst
  · exact compactTraceWeylSum_second_threshold_shrinking_saving f hc k j p hk hj hjk hmT hpT hsecond

/-- The literal optimized variable threshold, up to the critical moment,
now has an actual positive outer-minor saving. -/
theorem compactTraceWeylSum_optimized_shrinking_saving_below_critical
    (f : 𝓢(mixedSpace K, ℂ)) (hc : HasCompactSupport (f : mixedSpace K → ℂ))
    (k p : ℕ) (hk : 3≤k) (hpT : p≤k*(k+1))
    (hvariables : Thresholds.sufficientVariables k ≤ (p:ℤ)) :
    ∃ a C η : ℝ, 0<a ∧ a<1 ∧ 0<C ∧ 0<η ∧ ∀ (P : ℝ) (hP : 1≤P),
      (∫ q in shrinkingMinorArcs (K := K) k a P,
        ‖compactTraceWeylSum k f hc P (by linarith) q‖^p ∂traceHaar) ≤
        C*(P^finrank ℚ K : ℝ)^((p:ℝ)-k-η) := by
  have ht : Thresholds.threshold k < (p:ℚ) := by
    apply (Thresholds.strict_floor_threshold_minimal (Thresholds.threshold k) (p:ℤ)).mp
    simpa only [Thresholds.sufficientVariables, if_neg (show k≠2 by omega)] using hvariables
  exact compactTraceWeylSum_threshold_shrinking_saving f hc k p hk hpT ht

#print axioms compactTraceWeylSum_optimized_shrinking_saving_below_critical
end WaringSiegel.WSL4
