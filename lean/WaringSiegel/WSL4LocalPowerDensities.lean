import WaringSiegel.WSL4LocalPowerConvergence
import WaringSiegel.WSL3MomentLocalPowerOriginal

/-! # Actual general-degree local densities and uniform positive finite products

The density is the limit of the literal normalized quotient counts. Limit
existence for nonzero targets is proved at every prime; the finite-product
lower bound has no density-existence hypothesis.
-/
noncomputable section
open IsLocalRing Filter Topology
open scoped NumberField BigOperators
namespace WaringSiegel.WSL4Local
open WaringSiegel.WSL3

def localPowerDensity (R : Type*) [CommRing R] [IsLocalRing R]
    (k p : ℕ) (a : R) : ℝ :=
  limUnder atTop (fun e : ℕ => normalizedLocalPowerCount R k p e a)

theorem tendsto_localPowerDensity_of_ne_zero
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [Finite (ResidueField R)]
    (k p : ℕ) (hk : 0<k) (hp : 2≤p) (hk0 : (k:R)≠0)
    {a : R} (ha : a≠0) :
    Tendsto (fun e => normalizedLocalPowerCount R k p e a) atTop
      (𝓝 (localPowerDensity R k p a)) := by
  exact tendsto_nhds_limUnder
    (normalized_power_count_all_primes_tendsto_of_ne_zero k p hk hp hk0 ha)

theorem localPowerDensity_nonneg
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [Finite (ResidueField R)]
    (k p : ℕ) (hk : 0<k) (hp : 2≤p) (hk0 : (k:R)≠0)
    {a : R} (ha : a≠0) : 0≤localPowerDensity R k p a := by
  apply ge_of_tendsto (tendsto_localPowerDensity_of_ne_zero k p hk hp hk0 ha)
  exact Filter.Eventually.of_forall (fun e => by unfold normalizedLocalPowerCount; positivity)

variable {K : Type*} [Field K] [NumberField K]

def completionPowerDensity
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (k p : ℕ) (ν : 𝓞 K) : ℝ :=
  localPowerDensity (v.adicCompletionIntegers K) k p
    (algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν)

theorem tendsto_completionPowerDensity
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (k p : ℕ) (hk : 0<k) (hp : 2≤p) {ν : 𝓞 K} (hν : ν≠0) :
    Tendsto (fun e => normalizedLocalPowerCount (v.adicCompletionIntegers K) k p e
      (algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν)) atTop
      (𝓝 (completionPowerDensity v k p ν)) := by
  letI := completionIntegers_henselianLocalRing v
  letI := completionIntegers_residueFinite v
  letI := completionIntegers_charZero v
  have ha0 : algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν≠0 := by
    intro h
    apply hν
    apply FaithfulSMul.algebraMap_injective (𝓞 K) (v.adicCompletionIntegers K)
    simpa only [map_zero] using h
  exact tendsto_localPowerDensity_of_ne_zero k p hk hp (by exact_mod_cast hk.ne') ha0

theorem tendsto_original_power_density
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (k p : ℕ) (hk : 0<k) (hp : 2≤p) {ν : 𝓞 K} (hν : ν≠0) :
    Tendsto (fun e => normalizedPrimePowerCount v k p e ν) atTop
      (𝓝 (completionPowerDensity v k p ν)) := by
  simpa only [normalizedPrimePowerCount_eq_completion] using
    tendsto_completionPowerDensity v k p hk hp hν

theorem completionPowerDensity_uniform_lower
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (k p : ℕ) (hk : 0<k) (hp : 2≤p) {ν : 𝓞 K} (hν : ν≠0)
    (hlocal : LocalUnitSolvable k p ν) :
    completionPowerDensityLowerBound v k p ≤ completionPowerDensity v k p ν := by
  have he : p-1+1=p := by omega
  apply ge_of_tendsto (tendsto_completionPowerDensity v k p hk hp hν)
  apply eventually_atTop.mpr
  refine ⟨powerLocalPrecision (v.adicCompletionIntegers K) k,fun e hE => ?_⟩
  simpa only [he] using completion_normalized_power_count_lower_bound_all_primes
    v k (p-1) hk (by simpa only [he] using hlocal) hE

theorem completionPowerDensity_pos
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (k p : ℕ) (hk : 0<k) (hp : 2≤p) {ν : 𝓞 K} (hν : ν≠0)
    (hlocal : LocalUnitSolvable k p ν) : 0<completionPowerDensity v k p ν :=
  lt_of_lt_of_le (completionPowerDensityLowerBound_pos v k p)
    (completionPowerDensity_uniform_lower v k p hk hp hν hlocal)

theorem actual_power_densities_finite_products_uniform_positive
    (k p : ℕ) (hk : 0<k) (hp : 6≤p) :
    ∃ c : ℝ,0<c ∧ ∀ ν : 𝓞 K,ν≠0 → LocalUnitSolvable k p ν →
      ∀ S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
        c≤∏ v∈S,completionPowerDensity v k p ν := by
  obtain ⟨c,hc,hprod⟩ := completion_power_density_finite_products_uniform_positive
    (K:=K) k p hk hp
  refine ⟨c,hc,fun ν hν hlocal => ?_⟩
  exact hprod ν hlocal (fun v => completionPowerDensity v k p ν)
    (fun v => tendsto_completionPowerDensity v k p hk (by omega) hν)

#print axioms tendsto_original_power_density
#print axioms completionPowerDensity_uniform_lower
#print axioms actual_power_densities_finite_products_uniform_positive
end WaringSiegel.WSL4Local
