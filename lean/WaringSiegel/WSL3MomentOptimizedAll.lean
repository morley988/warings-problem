import WaringSiegel.WSL3MomentOptimizedMinor
import WaringSiegel.WSL3MomentSupercritical

/-! # Actual outer-minor saving at every integer above the optimized threshold -/
noncomputable section
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped BigOperators Classical NumberField SchwartzMap
namespace WaringSiegel.WSL3
open WSL2 WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

/-- Both full Hua families and the actual localized VMVT supply the
manuscript's optimized integer outer-minor estimate, uniformly in scale.
This does not assert the separate major-arc or representation endgame. -/
theorem compactTraceWeylSum_optimized_minor_saving
    (f : 𝓢(mixedSpace K, ℂ)) (hc : HasCompactSupport (f : mixedSpace K → ℂ))
    (k p : ℕ) (hk : 3≤k) (hvariables : Thresholds.sufficientVariables k ≤ (p:ℤ)) :
    ∃ C η : ℝ, 0<C ∧ 0<η ∧ ∀ (P : ℝ) (hP : 1≤P),
      (∫ q in vinogradovMinorArcs (K := K) k P,
        ‖compactTraceWeylSum k f hc P (by linarith) q‖^p ∂traceHaar) ≤
        C*(P^finrank ℚ K : ℝ)^((p:ℝ)-k-η) := by
  by_cases hpT : p≤k*(k+1)
  · exact compactTraceWeylSum_optimized_minor_saving_below_critical f hc k p hk hpT hvariables
  · exact compactTraceWeylSum_supercritical_minor_saving f hc k p hk (by omega)

#print axioms compactTraceWeylSum_optimized_minor_saving
end WaringSiegel.WSL3
