import WaringSiegel.WSL3LocalConductorShell

/-! # WSL3: actual local conductor coefficients telescope to local densities -/
noncomputable section
set_option maxHeartbeats 800000
open Filter Topology
open scoped BigOperators Classical NumberField
namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

def primePowerResidueFintype (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (e : ℕ) :
    Fintype (𝓞 K ⧸ v.asIdeal^e) := by
  letI := Ideal.finiteQuotientOfFreeOfNeBot (v.asIdeal^e) (pow_ne_zero e v.ne_bot)
  exact Fintype.ofFinite _

def primePowerPrimitiveCubicCoefficient
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (e : ℕ) (ν : 𝓞 K) : ℂ :=
  letI := primePowerResidueFintype v e
  ∑ ψ ∈ primitiveConductorCharacters (v.asIdeal^e),
    finiteRingPowerCharacterTerm 3 8 (Ideal.Quotient.mk (v.asIdeal^e) ν) ψ

theorem primePower_complete_cubic_character_sum
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (e : ℕ) (ν : 𝓞 K)
    [Fintype (𝓞 K ⧸ v.asIdeal^e)] :
    (∑ ψ : AddChar (𝓞 K ⧸ v.asIdeal^e) ℂ,
      finiteRingPowerCharacterTerm 3 8 (Ideal.Quotient.mk (v.asIdeal^e) ν) ψ) =
        (normalizedPrimePowerCubicCount v 8 e ν : ℂ) := by
  have hc : Fintype.card (𝓞 K ⧸ v.asIdeal^e) = Ideal.absNorm (v.asIdeal^e) := by
    rw [← Nat.card_eq_fintype_card, Ideal.absNorm_apply]
    rfl
  simpa only [finiteRingPowerCharacterTerm, hc] using
    (primePower_cubic_normalized_character_formula v e ν).symm

/-- The exact conductor-p^(e+1) coefficient is the difference between successive
literal normalized solution counts, including at ramified primes. -/
theorem primePowerPrimitiveCubicCoefficient_succ
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (e : ℕ) (ν : 𝓞 K) :
    primePowerPrimitiveCubicCoefficient v (e+1) ν =
      (normalizedPrimePowerCubicCount v 8 (e+1) ν : ℂ) -
        (normalizedPrimePowerCubicCount v 8 e ν : ℂ) := by
  letI := primePowerResidueFintype v e
  letI := primePowerResidueFintype v (e+1)
  unfold primePowerPrimitiveCubicCoefficient
  rw [primePower_primitive_characters_eq]
  rw [finite_ring_noninflated_character_sum _ (Ideal.Quotient.factor_surjective _),
    Ideal.Quotient.factor_mk, primePower_complete_cubic_character_sum,
    primePower_complete_cubic_character_sum]

theorem localCubicSolutionCount_top {R : Type*} [CommRing R] (s : ℕ) (a : R) :
    localCubicSolutionCount R ⊤ s a = 1 := by
  letI : Unique (LocalCubicSolutions R ⊤ s a) :=
    { default := ⟨fun _ => 0, Subsingleton.elim _ _⟩
      uniq := fun x => Subtype.ext (Subsingleton.elim _ _) }
  exact Nat.card_unique

@[simp] theorem normalizedPrimePowerCubicCount_zero
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (ν : 𝓞 K) :
    normalizedPrimePowerCubicCount v 8 0 ν = 1 := by
  simp only [normalizedPrimePowerCubicCount, pow_zero, Ideal.one_eq_top,
    localCubicSolutionCount_top, Nat.cast_one, mul_zero, div_one]

theorem primePowerPrimitiveCubicCoefficient_sum_range
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (n : ℕ) (ν : 𝓞 K) :
    (∑ e ∈ Finset.range n, primePowerPrimitiveCubicCoefficient v (e+1) ν) =
      (normalizedPrimePowerCubicCount v 8 n ν : ℂ) - 1 := by
  simp only [primePowerPrimitiveCubicCoefficient_succ]
  rw [Finset.sum_range_sub (fun e => (normalizedPrimePowerCubicCount v 8 e ν : ℂ)) n,
    normalizedPrimePowerCubicCount_zero, Complex.ofReal_one]

/-- For a nonzero target each local conductor series actually has finite
support; this follows from the proved stabilization of literal counts. -/
theorem primePowerPrimitiveCubicCoefficient_finite_support
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ν : 𝓞 K} (hν : ν ≠ 0) :
    (Function.support (fun e : ℕ => primePowerPrimitiveCubicCoefficient v (e+1) ν)).Finite := by
  obtain ⟨σ, E, hE⟩ := original_normalized_cubic_count_eventually_constant v hν
  apply (Finset.finite_toSet (Finset.range E)).subset
  intro e he
  change e ∈ Finset.range E
  rw [Finset.mem_range]
  by_contra h
  have heE : E ≤ e := Nat.le_of_not_gt h
  apply he
  change primePowerPrimitiveCubicCoefficient v (e+1) ν = 0
  rw [primePowerPrimitiveCubicCoefficient_succ, hE (e+1) (by omega), hE e heE, sub_self]

theorem primePowerPrimitiveCubicCoefficient_hasSum
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ν : 𝓞 K} (hν : ν ≠ 0)
    {σ : ℝ} (hσ : Tendsto (fun e => normalizedPrimePowerCubicCount v 8 e ν) atTop (𝓝 σ)) :
    HasSum (fun e : ℕ => primePowerPrimitiveCubicCoefficient v (e+1) ν) ((σ : ℂ)-1) := by
  have hs : Summable (fun e : ℕ => ‖primePowerPrimitiveCubicCoefficient v (e+1) ν‖) := by
    apply summable_of_finite_support
    simpa only [Function.support, norm_ne_zero_iff] using
      primePowerPrimitiveCubicCoefficient_finite_support v hν
  apply (hasSum_iff_tendsto_nat_of_summable_norm hs).mpr
  simp only [primePowerPrimitiveCubicCoefficient_sum_range]
  exact ((Complex.continuous_ofReal.tendsto σ).comp hσ).sub tendsto_const_nhds

end WaringSiegel

#print axioms WaringSiegel.primePowerPrimitiveCubicCoefficient_succ
#print axioms WaringSiegel.primePowerPrimitiveCubicCoefficient_hasSum
