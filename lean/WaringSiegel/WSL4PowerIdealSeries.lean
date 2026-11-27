import WaringSiegel.WSL4PowerCharacters
import WaringSiegel.WSL4LocalPowerDensities

/-! # Actual power coefficients grouped by conductor ideal

The grouped series is defined independently of the individual-character
tsum. No equality between those two infinite sums is assumed.
-/
noncomputable section
open Filter Topology
open scoped NumberField BigOperators Classical
namespace WaringSiegel.WSL4Local
open WaringSiegel.WSL3
variable {K : Type*} [Field K] [NumberField K]

def powerIdealSingularSeries (k p : ℕ) (ν : 𝓞 K) : ℂ :=
  ∑' I:{I:Ideal (𝓞 K)//I≠0},idealPrimitivePowerCoefficient k p I.1 I.2 ν

def primePowerPrimitivePowerCoefficient (k p : ℕ)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (e : ℕ) (ν : 𝓞 K) : ℂ :=
  idealPrimitivePowerCoefficient k p (v.asIdeal^e) (pow_ne_zero e v.ne_bot) ν

theorem primePower_complete_power_character_sum
    (k p : ℕ) (hp : 1≤p)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (e : ℕ) (ν : 𝓞 K)
    [Fintype (𝓞 K⧸v.asIdeal^e)] :
    (∑ ψ:AddChar (𝓞 K⧸v.asIdeal^e) ℂ,
      finiteRingPowerCharacterTerm k p (Ideal.Quotient.mk (v.asIdeal^e) ν) ψ)=
        (normalizedPrimePowerCount v k p e ν:ℂ) := by
  have hc : Fintype.card (𝓞 K⧸v.asIdeal^e)=Ideal.absNorm (v.asIdeal^e) := by
    rw [← Nat.card_eq_fintype_card,Ideal.absNorm_apply]
    rfl
  simpa only [finiteRingPowerCharacterTerm,hc] using
    (primePower_power_normalized_character_formula v k p e hp ν).symm

theorem primePowerPrimitivePowerCoefficient_succ
    (k p : ℕ) (hp : 1≤p)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (e : ℕ) (ν : 𝓞 K) :
    primePowerPrimitivePowerCoefficient k p v (e+1) ν=
      (normalizedPrimePowerCount v k p (e+1) ν:ℂ)-(normalizedPrimePowerCount v k p e ν:ℂ) := by
  letI := primePowerResidueFintype v e
  letI := primePowerResidueFintype v (e+1)
  unfold primePowerPrimitivePowerCoefficient idealPrimitivePowerCoefficient
  rw [primePower_primitive_characters_eq]
  rw [finite_ring_noninflated_character_sum _ (Ideal.Quotient.factor_surjective _),
    Ideal.Quotient.factor_mk,primePower_complete_power_character_sum k p hp,
    primePower_complete_power_character_sum k p hp]

theorem localPowerSolutionCount_top {R:Type*} [CommRing R] (k p:ℕ) (a:R) :
    localPowerSolutionCount R ⊤ k p a=1 := by
  letI : Unique (LocalPowerSolutions R ⊤ k p a) :=
    { default := ⟨fun _ => 0,Subsingleton.elim _ _⟩
      uniq := fun x => Subtype.ext (Subsingleton.elim _ _) }
  exact Nat.card_unique

@[simp] theorem normalizedLocalPowerCount_zero
    {R:Type*} [CommRing R] [IsLocalRing R] (k p:ℕ) (a:R) :
    normalizedLocalPowerCount R k p 0 a=1 := by
  simp only [normalizedLocalPowerCount,pow_zero,Ideal.one_eq_top,localPowerSolutionCount_top,
    Nat.cast_one,mul_zero,div_one]

@[simp] theorem normalizedPrimePowerCount_zero
    (k p:ℕ) (v:IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (ν:𝓞 K) :
    normalizedPrimePowerCount v k p 0 ν=1 := by
  simp only [normalizedPrimePowerCount,pow_zero,Ideal.one_eq_top,localPowerSolutionCount_top,
    Nat.cast_one,mul_zero,div_one]

theorem primePowerPrimitivePowerCoefficient_sum_range
    (k p:ℕ) (hp:1≤p) (v:IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (n:ℕ) (ν:𝓞 K) :
    (∑ e∈Finset.range n,primePowerPrimitivePowerCoefficient k p v (e+1) ν)=
      (normalizedPrimePowerCount v k p n ν:ℂ)-1 := by
  simp only [primePowerPrimitivePowerCoefficient_succ k p hp]
  rw [Finset.sum_range_sub (fun e => (normalizedPrimePowerCount v k p e ν:ℂ)) n,
    normalizedPrimePowerCount_zero,Complex.ofReal_one]

theorem primePowerPrimitivePowerCoefficient_finite_support
    (k p:ℕ) (hk:0<k) (hp:2≤p)
    (v:IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ν:𝓞 K} (hν:ν≠0) :
    (Function.support (fun e:ℕ => primePowerPrimitivePowerCoefficient k p v (e+1) ν)).Finite := by
  letI := completionIntegers_henselianLocalRing v
  letI := completionIntegers_residueFinite v
  letI := completionIntegers_charZero v
  have ha : algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν≠0 := by
    intro h
    apply hν
    apply FaithfulSMul.algebraMap_injective (𝓞 K) (v.adicCompletionIntegers K)
    simpa only [map_zero] using h
  obtain ⟨σ,E,hE⟩ := normalized_power_count_all_primes_eventually_constant_of_ne_zero
    k p hk hp (by exact_mod_cast hk.ne') ha
  apply (Finset.finite_toSet (Finset.range E)).subset
  intro e he
  change e∈Finset.range E
  rw [Finset.mem_range]
  by_contra h
  have heE : E≤e := Nat.le_of_not_gt h
  apply he
  change primePowerPrimitivePowerCoefficient k p v (e+1) ν=0
  rw [primePowerPrimitivePowerCoefficient_succ k p (by omega),
    normalizedPrimePowerCount_eq_completion,normalizedPrimePowerCount_eq_completion,
    hE (e+1) (by omega),hE e heE,sub_self]

theorem primePowerPrimitivePowerCoefficient_hasSum
    (k p:ℕ) (hk:0<k) (hp:2≤p)
    (v:IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ν:𝓞 K} (hν:ν≠0) :
    HasSum (fun e:ℕ => primePowerPrimitivePowerCoefficient k p v (e+1) ν)
      ((completionPowerDensity v k p ν:ℂ)-1) := by
  have hs : Summable (fun e:ℕ => ‖primePowerPrimitivePowerCoefficient k p v (e+1) ν‖) := by
    apply summable_of_finite_support
    simpa only [Function.support,norm_ne_zero_iff] using
      primePowerPrimitivePowerCoefficient_finite_support k p hk hp v hν
  apply (hasSum_iff_tendsto_nat_of_summable_norm hs).mpr
  simp only [primePowerPrimitivePowerCoefficient_sum_range k p (by omega)]
  exact ((Complex.continuous_ofReal.tendsto _).comp
    (tendsto_original_power_density v k p hk hp hν)).sub tendsto_const_nhds

#print axioms primePowerPrimitivePowerCoefficient_succ
#print axioms primePowerPrimitivePowerCoefficient_hasSum
end WaringSiegel.WSL4Local
