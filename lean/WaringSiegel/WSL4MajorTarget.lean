import WaringSiegel.WSL4MajorLowerBound
import WaringSiegel.WSL4PowerThreshold
import WaringSiegel.MainTargets

/-! # The unchanged all-field optimized large-k analytic target -/
noncomputable section
open scoped NumberField
namespace WaringSiegel.WSL4
open WSL2 WSL3 WSL4Local

theorem optimized_smoothRootMajorLowerBound
    {K : Type*} [Field K] [NumberField K]
    (k n : ℕ) (hk : 3≤k)
    (hvariables : Thresholds.sufficientVariables k≤(n:ℤ)) (B : ℝ) (hB : 0<B) :
    ∃ ρ R : ℝ, ∃ hρ : 0<ρ, ∃ hR : 0<R,
      SmoothMajorLowerBound (K := K) k n B ρ R hρ hR := by
  obtain ⟨hn,hkn⟩ := optimized_variables_arithmetic_range k n hk hvariables
  exact exists_smoothRootMajorLowerBound k n hk hn hkn hvariables B hB

theorem optimized_localConditionalBound
    (K : Type*) [Field K] [NumberField K] (k n : ℕ) (hk : 3≤k)
    (hvariables : Thresholds.sufficientVariables k≤(n:ℤ)) :
    LocalConditionalBound K k n := by
  obtain ⟨hn,_⟩ := optimized_variables_arithmetic_range k n hk hvariables
  obtain ⟨B,hB,_,hreduce⟩ := exists_compact_smoothMajor_reduction K k hk
  obtain ⟨ρ,R,hρ,hR,hmajor⟩ := optimized_smoothRootMajorLowerBound (K := K)
    k n hk hvariables B (lt_of_lt_of_le zero_lt_one hB)
  exact hreduce n (by omega) hvariables ρ R hρ hR hmajor

theorem largeKAnalyticClaim_verified : LargeKAnalyticClaim := by
  intro K _ _ k n hk hvariables
  exact optimized_localConditionalBound K k n hk hvariables

#print axioms optimized_smoothRootMajorLowerBound
#print axioms largeKAnalyticClaim_verified
end WaringSiegel.WSL4
