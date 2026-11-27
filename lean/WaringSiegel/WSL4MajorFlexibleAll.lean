import WaringSiegel.WSL4MajorFlexibleOptimized
import WaringSiegel.WSL4MajorFlexibleSupercritical

/-! # Actual smaller-cutoff minor saving at every integer above the optimized threshold -/
noncomputable section
open MeasureTheory NumberField NumberField.mixedEmbedding Module
open scoped BigOperators Classical NumberField SchwartzMap
namespace WaringSiegel.WSL4
open WSL2 WSL3 WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

/-- Both full Hua families and the actual localized VMVT supply the
manuscript's optimized integer smaller-cutoff minor estimate, uniformly in scale.
This does not assert the separate major-arc or representation endgame. -/
theorem compactTraceWeylSum_optimized_shrinking_saving
    (f : 𝓢(mixedSpace K, ℂ)) (hc : HasCompactSupport (f : mixedSpace K → ℂ))
    (k p : ℕ) (hk : 3≤k) (hvariables : Thresholds.sufficientVariables k ≤ (p:ℤ)) :
    ∃ a C η : ℝ, 0<a ∧ a<1 ∧ 0<C ∧ 0<η ∧ ∀ (P : ℝ) (hP : 1≤P),
      (∫ q in shrinkingMinorArcs (K := K) k a P,
        ‖compactTraceWeylSum k f hc P (by linarith) q‖^p ∂traceHaar) ≤
        C*(P^finrank ℚ K : ℝ)^((p:ℝ)-k-η) := by
  by_cases hpT : p≤k*(k+1)
  · exact compactTraceWeylSum_optimized_shrinking_saving_below_critical f hc k p hk hpT hvariables
  · exact compactTraceWeylSum_supercritical_shrinking_saving f hc k p hk (by omega)

#print axioms compactTraceWeylSum_optimized_shrinking_saving
end WaringSiegel.WSL4
