import WaringSiegel.WSL3CubicFiniteSharp
import WaringSiegel.WSL2LocalAuxiliaryDensity

/-! # WSL3: the manuscript cutoff 173 for actual modified local densities

The factors are the literal original prime-power congruence counts with
four unit coordinates. The product lower bound is uniform in the eligible
nonzero target and in every rational auxiliary prime p ≥ 173.
-/
noncomputable section
set_option maxHeartbeats 0
open IsLocalRing Filter Topology
open scoped NumberField BigOperators Classical
namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

theorem cubicModifiedResidueFactor_lower_173
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h6 : (6 : 𝓞 K) ∉ v.asIdeal) (hq : 173 ≤ Ideal.absNorm v.asIdeal) (ν : 𝓞 K) :
    (1 / 2 : ℝ) ≤ cubicModifiedResidueFactor v ν := by
  letI := completionIntegers_residueFinite v
  letI := Fintype.ofFinite (ResidueField (v.adicCompletionIntegers K))
  have h6' : (6 : ResidueField (v.adicCompletionIntegers K)) ≠ 0 :=
    fun h => h6 ((completion_residue_natCast_eq_zero_iff v 6).mp h)
  have hq' : 173 ≤ Fintype.card (ResidueField (v.adicCompletionIntegers K)) := by
    simpa only [← Nat.card_eq_fintype_card, completion_residue_card_eq_absNorm] using hq
  simpa only [cubicModifiedResidueFactor, ← Nat.card_eq_fintype_card,
    completion_residue_card_eq_absNorm] using
    finite_field_four_unit_cubic_normalized_lower_173 hq'
      (residue (v.adicCompletionIntegers K) (algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν))

theorem ordinary_cubic_factor_le_two_at_large_good_prime_173
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h6 : (6 : 𝓞 K) ∉ v.asIdeal) (hq : 173 ≤ Ideal.absNorm v.asIdeal)
    {ν : 𝓞 K} (hν0 : ν ≠ 0) {σ : ℝ}
    (hlim : Tendsto (fun e => normalizedPrimePowerCubicCount v 8 e ν) atTop (𝓝 σ)) :
    σ ≤ 2 := by
  have herror := original_good_prime_cubic_density_error_sq v h6 hν0 hlim
  have hqR : (173 : ℝ) ≤ Ideal.absNorm v.asIdeal := by exact_mod_cast hq
  have hqpos : 0 < (Ideal.absNorm v.asIdeal : ℝ) := by linarith
  have hpow : (576 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ 3 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 173) hqR 3
    norm_num at h
    linarith
  have he1 : (σ - 1) ^ 2 ≤ 1 := herror.trans ((div_le_one (pow_pos hqpos 3)).mpr hpow)
  have ha := abs_le_of_sq_le_sq (by simpa only [one_pow] using he1) (by norm_num : (0 : ℝ) ≤ 1)
  linarith [(abs_le.mp ha).2]

/-- One field-dependent constant survives replacing any finite set of
sufficiently large good-prime factors by their actual modified local factors. -/
theorem modified_cubic_euler_product_uniform_positive_173 :
    ∃ c : ℝ, 0 < c ∧ ∀ ν : 𝓞 K, Eligible 3 ν → ν ≠ 0 →
      ∃ σ : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ,
        (∀ v, 0 < σ v ∧ Tendsto (fun e => normalizedPrimePowerCubicCount v 8 e ν)
          atTop (𝓝 (σ v))) ∧
        ∀ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
          (∀ v ∈ S, (6 : 𝓞 K) ∉ v.asIdeal ∧ 173 ≤ Ideal.absNorm v.asIdeal) →
          Multipliable (fun v => if v ∈ S then cubicModifiedResidueFactor v ν else σ v) ∧
            c / (4 : ℝ) ^ S.card ≤
              ∏' v, if v ∈ S then cubicModifiedResidueFactor v ν else σ v := by
  obtain ⟨c, hc, hordinary⟩ := original_cubic_euler_product_uniform_positive (K := K)
  refine ⟨c, hc, ?_⟩
  intro ν hν hν0
  obtain ⟨σ, hσ, _, hmul, hbound⟩ := hordinary ν hν hν0
  refine ⟨σ, fun v => ⟨(hσ v).1, (hσ v).2.2⟩, ?_⟩
  intro S hS
  exact finite_replacement_product_lower σ (fun v => cubicModifiedResidueFactor v ν) S
    hmul (fun v => (hσ v).1)
    (fun v hv => ordinary_cubic_factor_le_two_at_large_good_prime_173 v
      (hS v hv).1 (hS v hv).2 hν0 (hσ v).2.2)
    (fun v hv => cubicModifiedResidueFactor_lower_173 v (hS v hv).1 (hS v hv).2 ν)
    hc hbound

/-- If at most m primes are modified, one constant works independently of the
chosen finite set and target. -/
theorem modified_cubic_euler_product_uniform_positive_of_card_le_173 (m : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ ν : 𝓞 K, Eligible 3 ν → ν ≠ 0 →
      ∃ σ : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ,
        (∀ v, 0 < σ v ∧ Tendsto (fun e => normalizedPrimePowerCubicCount v 8 e ν)
          atTop (𝓝 (σ v))) ∧
        ∀ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)), S.card ≤ m →
          (∀ v ∈ S, (6 : 𝓞 K) ∉ v.asIdeal ∧ 173 ≤ Ideal.absNorm v.asIdeal) →
          Multipliable (fun v => if v ∈ S then cubicModifiedResidueFactor v ν else σ v) ∧
            c ≤ ∏' v, if v ∈ S then cubicModifiedResidueFactor v ν else σ v := by
  obtain ⟨c, hc, hfamily⟩ := modified_cubic_euler_product_uniform_positive_173 (K := K)
  refine ⟨c / (4 : ℝ) ^ m, by positivity, ?_⟩
  intro ν hν hν0
  obtain ⟨σ, hσ, hreplace⟩ := hfamily ν hν hν0
  refine ⟨σ, hσ, ?_⟩
  intro S hcard hS
  obtain ⟨hmul, hbound⟩ := hreplace S hS
  refine ⟨hmul, le_trans ?_ hbound⟩
  exact div_le_div_of_nonneg_left hc.le (by positivity)
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hcard)

/-- The modified product has one positive lower bound for all eligible
nonzero targets and all rational auxiliary primes p≥173. -/
theorem auxiliary_prime_modified_cubic_euler_product_uniform_positive_173 :
    ∃ c : ℝ, 0 < c ∧ ∀ ν : 𝓞 K, Eligible 3 ν → ν ≠ 0 →
      ∃ σ : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ,
        (∀ v, 0 < σ v ∧ Tendsto (fun e => normalizedPrimePowerCubicCount v 8 e ν)
          atTop (𝓝 (σ v))) ∧
        ∀ (p : ℕ) (hp : p.Prime), 173 ≤ p →
          Multipliable (fun v => if v ∈ cubicAuxiliaryPrimeSet (K := K) p hp
            then cubicModifiedResidueFactor v ν else σ v) ∧
            c ≤ ∏' v, if v ∈ cubicAuxiliaryPrimeSet (K := K) p hp
              then cubicModifiedResidueFactor v ν else σ v := by
  obtain ⟨c, hc, hfamily⟩ :=
    modified_cubic_euler_product_uniform_positive_of_card_le_173 (K := K) (Module.finrank ℚ K)
  refine ⟨c, hc, ?_⟩
  intro ν hν hν0
  obtain ⟨σ, hσ, hreplace⟩ := hfamily ν hν hν0
  refine ⟨σ, hσ, ?_⟩
  intro p hp hlarge
  apply hreplace (cubicAuxiliaryPrimeSet (K := K) p hp)
  · exact prime_ideals_above_rational_prime_card_le hp _
      (fun v hv => (mem_cubicAuxiliaryPrimeSet hp v).mp hv)
  · intro v hv
    have hpv := (mem_cubicAuxiliaryPrimeSet hp v).mp hv
    exact ⟨prime_above_large_rational_prime_avoids_six v hp (by omega) hpv,
      hlarge.trans (rational_prime_le_residue_norm v hp hpv)⟩

theorem normalizedAuxiliaryPrimeCubicCount_of_mem_173
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    {p : ℕ} (hp : p.Prime) (hlarge : 173 ≤ p) (hpv : (p : 𝓞 K) ∈ v.asIdeal)
    (ν : 𝓞 K) (n : ℕ) :
    normalizedAuxiliaryPrimeCubicCount v p ν n = cubicModifiedResidueFactor v ν := by
  rw [normalizedAuxiliaryPrimeCubicCount, if_pos hpv]
  exact normalizedOriginalRestrictedCubicCount_eq_factor v
    (prime_above_large_rational_prime_avoids_six v hp (by omega) hpv) hpv ν n

/-- One positive field constant works for the limits of the literal local
congruence counts, simultaneously for every eligible nonzero target and
every auxiliary rational prime at or above the proved threshold. -/
theorem actual_auxiliary_cubic_local_densities_uniform_positive_173 :
    ∃ c : ℝ, 0 < c ∧ ∀ ν : 𝓞 K, Eligible 3 ν → ν ≠ 0 →
      ∀ (p : ℕ), p.Prime → 173 ≤ p →
        ∃ τ : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ,
          (∀ v, 0 < τ v ∧ Tendsto (normalizedAuxiliaryPrimeCubicCount v p ν)
            atTop (𝓝 (τ v))) ∧ Multipliable τ ∧ c ≤ ∏' v, τ v := by
  obtain ⟨c, hc, hfamily⟩ := auxiliary_prime_modified_cubic_euler_product_uniform_positive_173 (K := K)
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
        (cubicModifiedResidueFactor_lower_173 v
          (prime_above_large_rational_prime_avoids_six v hp (by omega) hpv)
          (hlarge.trans (rational_prime_le_residue_norm v hp hpv)) ν)
    · have heq : normalizedAuxiliaryPrimeCubicCount v p ν =
          fun _ : ℕ => cubicModifiedResidueFactor v ν := by
        funext n
        exact normalizedAuxiliaryPrimeCubicCount_of_mem_173 v hp hlarge hpv ν n
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

theorem original_restricted_cubic_count_lower_173
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h6 : (6 : 𝓞 K) ∉ v.asIdeal) (hq : 173 ≤ Ideal.absNorm v.asIdeal)
    {p : 𝓞 K} (hp : p ∈ v.asIdeal) (ν : 𝓞 K) (n : ℕ) :
    (1 / 2 : ℝ) ≤ normalizedOriginalRestrictedCubicCount v p ν n := by
  rw [normalizedOriginalRestrictedCubicCount_eq_factor v h6 hp]
  exact cubicModifiedResidueFactor_lower_173 v h6 hq ν


end WaringSiegel

#print axioms WaringSiegel.actual_auxiliary_cubic_local_densities_uniform_positive_173
#print axioms WaringSiegel.original_restricted_cubic_count_lower_173
