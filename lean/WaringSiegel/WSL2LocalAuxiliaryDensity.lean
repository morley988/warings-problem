import WaringSiegel.WSL2LocalScaledCount
import WaringSiegel.WSL2LocalModifiedCharacter

/-!
# The actual auxiliary-prime local densities and their uniformly positive product

At primes dividing the auxiliary rational prime, the count imposes the four
unit conditions. At all other primes no unit condition is imposed; scaling
the four y coordinates is a bijection. Both are literal original quotient
counts. Their limits form the previously proved modified Euler product.
-/

noncomputable section
set_option maxHeartbeats 0
open IsLocalRing Filter Topology
open scoped NumberField BigOperators Classical

namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

/-- Original prime-power congruence counts with precisely the local
coprimality conditions imposed by the auxiliary rational prime. The index n
corresponds to the positive precision n+1. -/
def normalizedAuxiliaryPrimeCubicCount
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (p : ℕ) (ν : 𝓞 K) (n : ℕ) : ℝ :=
  if (p : 𝓞 K) ∈ v.asIdeal then normalizedOriginalRestrictedCubicCount v (p : 𝓞 K) ν n
  else (Nat.card (ScaledLocalCubicSolutions (𝓞 K) (v.asIdeal ^ (n + 1)) (p : 𝓞 K) ν) : ℝ) /
    (Ideal.absNorm v.asIdeal : ℝ) ^ (7 * (n + 1))

theorem normalizedAuxiliaryPrimeCubicCount_of_mem
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {p : ℕ} (hp : p.Prime) (hlarge : 24576 ≤ p) (hpv : (p : 𝓞 K) ∈ v.asIdeal)
    (ν : 𝓞 K) (n : ℕ) :
    normalizedAuxiliaryPrimeCubicCount v p ν n = cubicModifiedResidueFactor v ν := by
  rw [normalizedAuxiliaryPrimeCubicCount, if_pos hpv]
  exact normalizedOriginalRestrictedCubicCount_eq_factor v
    (prime_above_large_rational_prime_avoids_six v hp (by omega) hpv) hpv ν n

theorem normalizedAuxiliaryPrimeCubicCount_of_not_mem
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {p : ℕ} (hpv : (p : 𝓞 K) ∉ v.asIdeal) (ν : 𝓞 K) (n : ℕ) :
    normalizedAuxiliaryPrimeCubicCount v p ν n = normalizedPrimePowerCubicCount v 8 (n + 1) ν := by
  rw [normalizedAuxiliaryPrimeCubicCount, if_neg hpv, original_scaled_cubic_count_eq_ordinary v hpv]
  rfl

/-- One positive field constant works for the limits of the literal local
congruence counts, simultaneously for every eligible nonzero target and
every auxiliary rational prime at or above the proved threshold. -/
theorem actual_auxiliary_cubic_local_densities_uniform_positive :
    ∃ c : ℝ, 0 < c ∧ ∀ ν : 𝓞 K, Eligible 3 ν → ν ≠ 0 →
      ∀ (p : ℕ), p.Prime → 24576 ≤ p →
        ∃ τ : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ,
          (∀ v, 0 < τ v ∧ Tendsto (normalizedAuxiliaryPrimeCubicCount v p ν)
            atTop (𝓝 (τ v))) ∧ Multipliable τ ∧ c ≤ ∏' v, τ v := by
  obtain ⟨c, hc, hfamily⟩ := auxiliary_prime_modified_cubic_euler_product_uniform_positive (K := K)
  refine ⟨c, hc, ?_⟩
  intro ν hν hν0 p hp hlarge
  obtain ⟨σ, hσ, hmodified⟩ := hfamily ν hν hν0
  let τ := fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
    if v ∈ cubicAuxiliaryPrimeSet (K := K) p hp then cubicModifiedResidueFactor v ν else σ v
  obtain ⟨hmul, hbound⟩ := hmodified p hp hlarge
  refine ⟨τ, ?_, hmul, hbound⟩
  intro v
  by_cases hpv : (p : 𝓞 K) ∈ v.asIdeal
  · have hmem : v ∈ cubicAuxiliaryPrimeSet (K := K) p hp :=
      (mem_cubicAuxiliaryPrimeSet hp v).mpr hpv
    dsimp only [τ]
    rw [if_pos hmem]
    constructor
    · exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
        (cubicModifiedResidueFactor_lower v
          (prime_above_large_rational_prime_avoids_six v hp (by omega) hpv)
          (hlarge.trans (rational_prime_le_residue_norm v hp hpv)) ν)
    · have heq : normalizedAuxiliaryPrimeCubicCount v p ν =
          fun _ : ℕ => cubicModifiedResidueFactor v ν := by
        funext n
        exact normalizedAuxiliaryPrimeCubicCount_of_mem v hp hlarge hpv ν n
      rw [heq]
      exact tendsto_const_nhds
  · have hnmem : v ∉ cubicAuxiliaryPrimeSet (K := K) p hp :=
      fun h => hpv ((mem_cubicAuxiliaryPrimeSet hp v).mp h)
    dsimp only [τ]
    rw [if_neg hnmem]
    constructor
    · exact (hσ v).1
    · have heq : normalizedAuxiliaryPrimeCubicCount v p ν =
          fun n : ℕ => normalizedPrimePowerCubicCount v 8 (n + 1) ν := by
        funext n
        exact normalizedAuxiliaryPrimeCubicCount_of_not_mem v hpv ν n
      rw [heq]
      exact (hσ v).2.comp (tendsto_add_atTop_nat 1)

end WaringSiegel

#print axioms WaringSiegel.actual_auxiliary_cubic_local_densities_uniform_positive
