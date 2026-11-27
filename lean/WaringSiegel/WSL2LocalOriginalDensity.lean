import WaringSiegel.WSL2LocalPrimePowerQuotient
import WaringSiegel.WSL2CubicEulerProduct

/-!
# Cubic densities in the original number-field residue rings

The completion comparison transports the literal solution counts modulo
𝔭^e. Therefore the local limits and their uniformly positive Euler product
are limits of the original congruence counts used in the singular series.
-/

noncomputable section
open IsLocalRing Filter Topology
open scoped NumberField BigOperators

namespace WaringSiegel

/-- Quotient-ring equivalences preserving the target preserve literal cubic counts. -/
theorem localCubicSolutionCount_congr
    {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (s : ℕ) (a : R) (b : S)
    (e : (R ⧸ I) ≃+* (S ⧸ J))
    (hab : e (Ideal.Quotient.mk I a) = Ideal.Quotient.mk J b) :
    localCubicSolutionCount R I s a = localCubicSolutionCount S J s b := by
  unfold localCubicSolutionCount
  apply Nat.card_congr
  exact
    { toFun := fun x => ⟨fun i => e (x.val i), by
        change (∑ i, e (x.val i) ^ 3) = _
        simpa only [map_sum, map_pow] using (congrArg e x.property).trans hab⟩
      invFun := fun y => ⟨fun i => e.symm (y.val i), by
        apply e.injective
        rw [map_sum]
        simp only [map_pow, e.apply_symm_apply]
        exact y.property.trans hab.symm⟩
      left_inv := fun x => by apply Subtype.ext; funext i; exact e.symm_apply_apply _
      right_inv := fun y => by apply Subtype.ext; funext i; exact e.apply_symm_apply _ }

variable {K : Type*} [Field K] [NumberField K]

/-- Original and completed cubic congruence counts agree at every exponent. -/
theorem primePower_cubic_solution_count_eq
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (e s : ℕ) (ν : 𝓞 K) :
    localCubicSolutionCount (𝓞 K) (v.asIdeal ^ e) s ν =
      localCubicSolutionCount (v.adicCompletionIntegers K)
        (maximalIdeal (v.adicCompletionIntegers K) ^ e) s
        (algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν) := by
  apply localCubicSolutionCount_congr _ _ _ _ _ (primePowerCompletionEquiv v e)
  rfl

/-- The normalized count is expressed entirely in the original finite quotient. -/
def normalizedPrimePowerCubicCount
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (s e : ℕ) (ν : 𝓞 K) : ℝ :=
  (localCubicSolutionCount (𝓞 K) (v.asIdeal ^ e) s ν : ℝ) /
    (Ideal.absNorm v.asIdeal : ℝ) ^ ((s - 1) * e)

theorem normalizedPrimePowerCubicCount_eq_completion
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (s e : ℕ) (ν : 𝓞 K) :
    normalizedPrimePowerCubicCount v s e ν =
      normalizedLocalCubicCount (v.adicCompletionIntegers K) s e
        (algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν) := by
  unfold normalizedPrimePowerCubicCount normalizedLocalCubicCount
  rw [primePower_cubic_solution_count_eq, completion_residue_card_eq_absNorm]

theorem original_cubic_density_exists_positive
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {ν : 𝓞 K} (hν : Eligible 3 ν) (hν0 : ν ≠ 0) :
    ∃ σ : ℝ, 0 < σ ∧ completionCubicDensityLowerBound v ≤ σ ∧
      Tendsto (fun e => normalizedPrimePowerCubicCount v 8 e ν) atTop (𝓝 σ) := by
  simpa only [normalizedPrimePowerCubicCount_eq_completion] using
    completion_cubic_density_exists_positive v hν hν0

/-- One positive constant works for the original congruence-count Euler product
for every eligible nonzero target. -/
theorem original_cubic_euler_product_uniform_positive :
    ∃ c : ℝ, 0 < c ∧ ∀ ν : 𝓞 K, Eligible 3 ν → ν ≠ 0 →
      ∃ σ : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ,
        (∀ v, 0 < σ v ∧ completionCubicDensityLowerBound v ≤ σ v ∧
          Tendsto (fun e => normalizedPrimePowerCubicCount v 8 e ν) atTop (𝓝 (σ v))) ∧
        Summable (fun v => |σ v - 1|) ∧ Multipliable σ ∧ c ≤ ∏' v, σ v := by
  simpa only [normalizedPrimePowerCubicCount_eq_completion] using
    completion_cubic_euler_product_uniform_positive (K := K)

/-- The target-uniform lower bound is also an explicit count in the original ring. -/
theorem original_cubic_prime_power_count_lower_bound
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {ν : 𝓞 K} (hν : Eligible 3 ν) (n : ℕ) :
    (Ideal.absNorm v.asIdeal) ^ (7 * n) ≤
      localCubicSolutionCount (𝓞 K)
        (v.asIdeal ^ (n + cubicLocalPrecision (v.adicCompletionIntegers K))) 8 ν := by
  rw [primePower_cubic_solution_count_eq]
  simpa only [completion_residue_card_eq_absNorm] using
    completion_cubic_count_lower_bound v hν n

/-- Good-prime error in original congruence-count notation, uniform in the target. -/
theorem original_good_prime_cubic_density_error_sq
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h6 : (6 : 𝓞 K) ∉ v.asIdeal) {ν : 𝓞 K} (hν0 : ν ≠ 0)
    {σ : ℝ} (hlim : Tendsto (fun e => normalizedPrimePowerCubicCount v 8 e ν)
      atTop (𝓝 σ)) :
    (σ - 1) ^ 2 ≤ 576 / (Ideal.absNorm v.asIdeal : ℝ) ^ 3 := by
  have h6' : (6 : ResidueField (v.adicCompletionIntegers K)) ≠ 0 :=
    fun h => h6 ((completion_residue_natCast_eq_zero_iff v 6).mp h)
  have hlim' := hlim
  simp only [normalizedPrimePowerCubicCount_eq_completion] at hlim'
  simpa only [completion_residue_card_eq_absNorm] using
    completion_good_prime_cubic_density_error_sq v h6' hν0 hlim'

/-- Every nonzero original target has eventually constant normalized counts;
eligibility is needed for positivity, not for convergence. -/
theorem original_normalized_cubic_count_eventually_constant
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {ν : 𝓞 K} (hν0 : ν ≠ 0) :
    ∃ σ : ℝ, ∃ E : ℕ, ∀ e ≥ E, normalizedPrimePowerCubicCount v 8 e ν = σ := by
  letI := completionIntegers_henselianLocalRing v
  letI := completionIntegers_residueFinite v
  letI := completionIntegers_charZero v
  have ha0 : algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν ≠ 0 := by
    intro h
    apply hν0
    apply FaithfulSMul.algebraMap_injective (𝓞 K) (v.adicCompletionIntegers K)
    simpa only [map_zero] using h
  simpa only [normalizedPrimePowerCubicCount_eq_completion] using
    normalized_cubic_count_all_primes_eventually_constant_of_ne_zero
      (R := v.adicCompletionIntegers K) (by norm_num) ha0

end WaringSiegel

#print axioms WaringSiegel.primePower_cubic_solution_count_eq
#print axioms WaringSiegel.original_cubic_density_exists_positive

#print axioms WaringSiegel.original_cubic_euler_product_uniform_positive
#print axioms WaringSiegel.original_cubic_prime_power_count_lower_bound

#print axioms WaringSiegel.original_good_prime_cubic_density_error_sq
#print axioms WaringSiegel.original_normalized_cubic_count_eventually_constant
