import WaringSiegel.WSL2LocalAllPrimeConvergence
import WaringSiegel.WSL2LocalTargets

/-!
# Positive cubic local densities at every number-field prime

These theorems combine genuine local-density convergence with the explicit,
target-uniform lower bound at all finite primes, including those above 3.
Only eligibility and a nonzero target remain in the main interface.
-/

noncomputable section

open IsLocalRing Filter Topology
open scoped NumberField BigOperators

namespace WaringSiegel

variable {K : Type*} [Field K] [NumberField K]

/-- Every actual finite completion has a convergent positive eight-cube local
density. The lower bound is `q^(-7(2v(3)+1))` and is independent of the target. -/
theorem completion_cubic_density_exists_positive
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {ν : 𝓞 K} (hν : Eligible 3 ν) (hν0 : ν ≠ 0) :
    ∃ σ : ℝ, 0 < σ ∧ completionCubicDensityLowerBound v ≤ σ ∧
      Tendsto (fun e => normalizedLocalCubicCount (v.adicCompletionIntegers K) 8 e
        (algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν)) atTop (𝓝 σ) := by
  letI := completionIntegers_henselianLocalRing v
  letI := completionIntegers_residueFinite v
  letI := completionIntegers_charZero v
  have ha0 : algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν ≠ 0 := by
    intro h
    apply hν0
    apply FaithfulSMul.algebraMap_injective (𝓞 K) (v.adicCompletionIntegers K)
    simpa only [map_zero] using h
  obtain ⟨σ, hlim⟩ := normalized_cubic_count_all_primes_tendsto_of_ne_zero
    (R := v.adicCompletionIntegers K) (by norm_num) ha0
  have hbound := completion_cubic_density_limit_lower_bound v hν hlim
  exact ⟨σ, lt_of_lt_of_le (completionCubicDensityLowerBound_pos v) hbound, hbound, hlim⟩

/-- A simultaneous family of the actual local densities, with explicit
positive lower bounds proved rather than assumed. -/
theorem completion_cubic_density_family_exists
    {ν : 𝓞 K} (hν : Eligible 3 ν) (hν0 : ν ≠ 0) :
    ∃ σ : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ, ∀ v,
      0 < σ v ∧ completionCubicDensityLowerBound v ≤ σ v ∧
        Tendsto (fun e => normalizedLocalCubicCount (v.adicCompletionIntegers K) 8 e
          (algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν)) atTop (𝓝 (σ v)) := by
  choose σ hσ using fun v => completion_cubic_density_exists_positive v hν hν0
  exact ⟨σ, hσ⟩

/-- A uniform positive lower bound for any finite exceptional-prime product. -/
theorem finite_cubic_local_density_product_lower
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    {ν : 𝓞 K} (hν : Eligible 3 ν)
    (σ : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ)
    (hσ : ∀ v, Tendsto (fun e => normalizedLocalCubicCount (v.adicCompletionIntegers K) 8 e
      (algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν)) atTop (𝓝 (σ v))) :
    0 < (∏ v ∈ S, completionCubicDensityLowerBound v) ∧
      (∏ v ∈ S, completionCubicDensityLowerBound v) ≤ ∏ v ∈ S, σ v := by
  constructor
  · exact Finset.prod_pos (fun v _ => completionCubicDensityLowerBound_pos v)
  · exact Finset.prod_le_prod
      (fun v _ => (completionCubicDensityLowerBound_pos v).le)
      (fun v _ => completion_cubic_density_limit_lower_bound v hν (hσ v))

end WaringSiegel

#print axioms WaringSiegel.completion_cubic_density_exists_positive
#print axioms WaringSiegel.completion_cubic_density_family_exists
#print axioms WaringSiegel.finite_cubic_local_density_product_lower
