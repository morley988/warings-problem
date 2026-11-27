import WaringSiegel.WSL2LocalConvergence

/-!
# Quantitative cubic local theorems over actual number-field completions

This interface combines the proved completion infrastructure, all-prime
uniform lower bounds, and density convergence away from primes over 3.
-/

noncomputable section

open IsLocalRing Filter Topology
open scoped NumberField BigOperators

namespace WaringSiegel

variable {K : Type*} [Field K] [NumberField K]

theorem completion_cubic_density_limit_lower_bound
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {ν : 𝓞 K} (hν : Eligible 3 ν) {σ : ℝ}
    (hlim : Tendsto (fun e => normalizedLocalCubicCount
      (v.adicCompletionIntegers K) 8 e
        (algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν)) atTop (𝓝 σ)) :
    completionCubicDensityLowerBound v ≤ σ := by
  apply ge_of_tendsto hlim
  exact eventually_atTop.mpr ⟨cubicLocalPrecision (v.adicCompletionIntegers K),
    fun e he => completion_normalized_cubic_count_lower_bound v hν he⟩

/-- No convergence hypothesis remains at primes where 3 is a unit. The lower
bound is uniform in the nonzero eligible target and explicit in the local ring. -/
theorem completion_cubic_density_exists_positive_away_three
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h3 : IsUnit (3 : v.adicCompletionIntegers K))
    {ν : 𝓞 K} (hν : Eligible 3 ν) (hν0 : ν ≠ 0) :
    ∃ σ : ℝ, 0 < σ ∧ completionCubicDensityLowerBound v ≤ σ ∧
      Tendsto (fun e => normalizedLocalCubicCount (v.adicCompletionIntegers K) 8 e
        (algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν)) atTop (𝓝 σ) := by
  letI := completionIntegers_henselianLocalRing v
  letI := completionIntegers_residueFinite v
  have ha0 : algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν ≠ 0 := by
    intro h
    apply hν0
    apply FaithfulSMul.algebraMap_injective (𝓞 K) (v.adicCompletionIntegers K)
    simpa only [map_zero] using h
  obtain ⟨σ, hlim⟩ := normalized_cubic_count_tendsto_of_ne_zero h3 ha0
  have hbound := completion_cubic_density_limit_lower_bound v hν hlim
  exact ⟨σ, lt_of_lt_of_le (completionCubicDensityLowerBound_pos v) hbound, hbound, hlim⟩

end WaringSiegel

#print axioms WaringSiegel.completion_cubic_density_exists_positive_away_three
