import WaringSiegel.WSL4PowerSeriesEuler
import WaringSiegel.WSL3MomentThresholdRange
import WaringSiegel.VerifiedThresholdTable

/-! # The exact optimized threshold supplies all arithmetic-series hypotheses -/
noncomputable section
open scoped NumberField
namespace WaringSiegel.WSL4Local

theorem optimized_variables_arithmetic_range (k p : ℕ) (hk : 3 ≤ k)
    (hp : Thresholds.sufficientVariables k ≤ (p : ℤ)) : 8 ≤ p ∧ k + 3 ≤ p := by
  have h := Thresholds.admissible_variables_gt_twice_degree k p hk hp
  by_cases hk3 : k = 3
  · subst k
    rw [Thresholds.variables_3] at hp
    omega
  · omega

theorem optimized_powerIdealSingularSeries_uniform_positive
    {K : Type*} [Field K] [NumberField K]
    (k p : ℕ) (hk : 3 ≤ k)
    (hp : Thresholds.sufficientVariables k ≤ (p : ℤ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ ν : 𝓞 K, ν ≠ 0 → LocalUnitSolvable k p ν →
      Summable (fun I : {I : Ideal (𝓞 K) // I ≠ 0} =>
        ‖idealPrimitivePowerCoefficient k p I.1 I.2 ν‖) ∧
      (powerIdealSingularSeries k p ν).im = 0 ∧
      c ≤ (powerIdealSingularSeries k p ν).re := by
  obtain ⟨hp8,hkp⟩ := optimized_variables_arithmetic_range k p hk hp
  exact powerIdealSingularSeries_uniform_positive k p (by omega) hp8 hkp

#print axioms optimized_variables_arithmetic_range
#print axioms optimized_powerIdealSingularSeries_uniform_positive
end WaringSiegel.WSL4Local
