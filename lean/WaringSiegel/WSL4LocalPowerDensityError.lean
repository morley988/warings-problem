import WaringSiegel.WSL4LocalPowerDensityUpper

/-! # Summable, target-uniform errors of the actual good-prime densities -/
noncomputable section
open IsLocalRing Filter Topology
open scoped NumberField BigOperators
namespace WaringSiegel.WSL4Local
open WaringSiegel.WSL3

theorem localPowerDensity_good_error
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [Finite (ResidueField R)]
    (k p : ℕ) (hk : 0<k) (hp : 6≤p) (hkp : k+2≤p)
    (hku : IsUnit (k:R)) {a : R} (ha : a≠0) :
    |localPowerDensity R k p a-1|≤
      2*((((k-1:ℕ):ℝ)^6+1)/(Nat.card (ResidueField R):ℝ)^2) := by
  have hk' : k-1+1=k := by omega
  have hp' : p-2+2=p := by omega
  have hupper := localPowerDensity_good_upper_error (R:=R) (k-1) (p-2)
    (by omega) (by omega) (by simpa only [hk'] using hku) ha
  simp only [hk',hp'] at hupper
  have ht := (tendsto_localPowerDensity_of_ne_zero k p hk (by omega) hku.ne_zero ha).comp
    (tendsto_add_atTop_nat 1)
  have hlower : 1-((((k-1:ℕ):ℝ)^6+1)/(Nat.card (ResidueField R):ℝ)^2)
      ≤localPowerDensity R k p a := by
    apply ge_of_tendsto ht
    exact Filter.Eventually.of_forall (fun n =>
      normalized_local_power_all_variables_good_tail k p hk hp hku n a)
  have he : 0≤((((k-1:ℕ):ℝ)^6+1)/(Nat.card (ResidueField R):ℝ)^2) := by positivity
  apply abs_le.mpr
  constructor
  · linarith
  · calc
      _ ≤ 2*((((k-1:ℕ):ℝ)^6+1))/(Nat.card (ResidueField R):ℝ)^2 := hupper
      _ = _ := by ring

variable {K : Type*} [Field K] [NumberField K]

theorem completionPowerDensity_good_error
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (k p : ℕ) (hk : 0<k) (hp : 6≤p) (hkp : k+2≤p)
    (hku : IsUnit (k:v.adicCompletionIntegers K)) {ν : 𝓞 K} (hν : ν≠0) :
    |completionPowerDensity v k p ν-1|≤2*powerEulerLowerError (K:=K) k 3 v := by
  letI := completionIntegers_henselianLocalRing v
  letI := completionIntegers_residueFinite v
  have ha : algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν≠0 := by
    intro h
    apply hν
    apply FaithfulSMul.algebraMap_injective (𝓞 K) (v.adicCompletionIntegers K)
    simpa only [map_zero] using h
  simpa only [completionPowerDensity,powerEulerLowerError,completion_residue_card_eq_absNorm]
    using localPowerDensity_good_error k p hk hp hkp hku ha

theorem completionPowerDensity_error_summable
    (k p : ℕ) (hk : 0<k) (hp : 6≤p) (hkp : k+2≤p)
    {ν : 𝓞 K} (hν : ν≠0) :
    Summable (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      |completionPowerDensity v k p ν-1|) := by
  apply Summable.of_norm_bounded_eventually ((powerEulerLowerError_summable (K:=K) k 3).mul_left 2)
  filter_upwards [good_power_completion_primes_cofinite (K:=K) k hk] with v hv
  simpa only [Real.norm_eq_abs,abs_abs] using completionPowerDensity_good_error v k p hk hp hkp hv hν

#print axioms localPowerDensity_good_error
#print axioms completionPowerDensity_good_error
#print axioms completionPowerDensity_error_summable
end WaringSiegel.WSL4Local
