import WaringSiegel.WSL4PowerWeightedSeries

/-! # A target-independent summable majorant for the actual weighted local coefficients -/
noncomputable section
set_option maxHeartbeats 1400000
open IsLocalRing Filter Topology
open scoped NumberField BigOperators Classical
namespace WaringSiegel.WSL4Local
open WaringSiegel.WSL3
variable {K:Type*} [Field K] [NumberField K]

def powerPrimeConductorWeight (k:ℕ)
    (v:IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (e:ℕ) : ℝ :=
  (Ideal.absNorm v.asIdeal:ℝ)^(e/k+1)

def weightedLocalPowerCoefficient (k p:ℕ)
    (v:IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (e:ℕ) (ν:𝓞 K) : ℝ :=
  powerPrimeConductorWeight k v e*‖primePowerPrimitivePowerCoefficient k p v (e+1) ν‖

theorem weightedLocalPowerCoefficient_nonneg (k p:ℕ)
    (v:IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (e:ℕ) (ν:𝓞 K) :
    0≤weightedLocalPowerCoefficient k p v e ν := by
  unfold weightedLocalPowerCoefficient powerPrimeConductorWeight
  positivity

theorem weightedLocalPowerCoefficient_eq_completion (k p:ℕ) (hp:1≤p)
    (v:IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (e:ℕ) (ν:𝓞 K) :
    weightedLocalPowerCoefficient k p v e ν=
      weightedPowerIncrement (v.adicCompletionIntegers K) k p
        (algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν) e := by
  simp only [weightedLocalPowerCoefficient,powerPrimeConductorWeight,
    primePowerPrimitivePowerCoefficient_succ k p hp,← Complex.ofReal_sub,
    Complex.norm_real,Real.norm_eq_abs,normalizedPrimePowerCount_eq_completion,
    weightedPowerIncrement,powerConductorWeight,completion_residue_card_eq_absNorm]

def powerUniformLocalWeightedMass (k:ℕ)
    (v:IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ℝ :=
  if IsUnit (k:v.adicCompletionIntegers K) then
    4*(k:ℝ)*(((k-1:ℕ):ℝ)^8+1)/(Ideal.absNorm v.asIdeal:ℝ)^2
  else powerBadPrimeWeightedMass (v.adicCompletionIntegers K) k

theorem powerUniformLocalWeightedMass_nonneg (k:ℕ)
    (v:IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : 0≤powerUniformLocalWeightedMass k v := by
  unfold powerUniformLocalWeightedMass powerBadPrimeWeightedMass
  split_ifs <;> positivity

theorem powerUniformLocalWeightedMass_summable (k:ℕ) (hk:0<k) :
    Summable (powerUniformLocalWeightedMass (K:=K) k) := by
  have h:Summable (fun v:IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      4*(k:ℝ)*(((k-1:ℕ):ℝ)^8+1)/(Ideal.absNorm v.asIdeal:ℝ)^2) := by
    have hs := (primeIdeal_norm_rpow_summable (K:=K) (by norm_num : (1:ℝ)<2)).mul_left
      (4*(k:ℝ)*(((k-1:ℕ):ℝ)^8+1))
    convert hs using 1
    funext v
    rw [Real.rpow_neg (Nat.cast_nonneg _)]
    norm_num [Real.rpow_natCast,div_eq_mul_inv]
  apply h.congr_cofinite
  filter_upwards [good_power_completion_primes_cofinite (K:=K) k hk] with v hv
  simp only [powerUniformLocalWeightedMass,if_pos hv]

theorem weightedLocalPowerCoefficient_summable_bound
    (k p:ℕ) (hk:0<k) (hp:8≤p) (hkp:k+3≤p)
    (v:IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (ν:𝓞 K) :
    Summable (fun e => weightedLocalPowerCoefficient k p v e ν) ∧
      (∑' e,weightedLocalPowerCoefficient k p v e ν)≤powerUniformLocalWeightedMass k v := by
  letI := completionIntegers_henselianLocalRing v
  letI := completionIntegers_residueFinite v
  letI := completionIntegers_charZero v
  simp only [weightedLocalPowerCoefficient_eq_completion k p (by omega)]
  unfold powerUniformLocalWeightedMass
  split_ifs with hku
  · simpa only [completion_residue_card_eq_absNorm] using
      weightedPowerIncrement_good_summable_bound k p hk hp hkp hku
        (algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν)
  · exact weightedPowerIncrement_all_primes_summable_bound k p hk (by omega) (by omega)
      (by exact_mod_cast hk.ne') (algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν)

theorem weightedLocalPowerCoefficient_global_summable
    (k p:ℕ) (hk:0<k) (hp:8≤p) (hkp:k+3≤p) (ν:𝓞 K) :
    Summable (fun ve:IsDedekindDomain.HeightOneSpectrum (𝓞 K)×ℕ =>
      weightedLocalPowerCoefficient k p ve.1 ve.2 ν) := by
  apply (summable_prod_of_nonneg (fun ve => weightedLocalPowerCoefficient_nonneg k p ve.1 ve.2 ν)).mpr
  refine ⟨fun v => (weightedLocalPowerCoefficient_summable_bound k p hk hp hkp v ν).1,?_⟩
  apply (powerUniformLocalWeightedMass_summable k hk).of_nonneg_of_le
    (fun v => tsum_nonneg (fun e => weightedLocalPowerCoefficient_nonneg k p v e ν))
  intro v
  exact (weightedLocalPowerCoefficient_summable_bound k p hk hp hkp v ν).2

theorem weightedLocalPowerCoefficient_global_tsum_le
    (k p:ℕ) (hk:0<k) (hp:8≤p) (hkp:k+3≤p) (ν:𝓞 K) :
    (∑' ve:IsDedekindDomain.HeightOneSpectrum (𝓞 K)×ℕ,weightedLocalPowerCoefficient k p ve.1 ve.2 ν)≤
      ∑' v:IsDedekindDomain.HeightOneSpectrum (𝓞 K),powerUniformLocalWeightedMass k v := by
  rw [(weightedLocalPowerCoefficient_global_summable k p hk hp hkp ν).tsum_prod]
  apply Summable.tsum_le_tsum (fun v => (weightedLocalPowerCoefficient_summable_bound k p hk hp hkp v ν).2)
  · exact (weightedLocalPowerCoefficient_global_summable k p hk hp hkp ν).prod
  · exact powerUniformLocalWeightedMass_summable k hk

#print axioms weightedLocalPowerCoefficient_global_summable
#print axioms weightedLocalPowerCoefficient_global_tsum_le
end WaringSiegel.WSL4Local
