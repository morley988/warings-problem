import WaringSiegel.WSL3LocalWeightedSeries
import WaringSiegel.WSL3ConductorIdealSeries

/-! # WSL3: a summable target-independent majorant for weighted local masses -/
noncomputable section
open IsLocalRing Filter Topology
open scoped BigOperators Classical NumberField
namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

def primePowerConductorWeight
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (e : ℕ) : ℝ :=
  (Ideal.absNorm v.asIdeal : ℝ)^(e/3+1)

def weightedLocalCubicCoefficient
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (e : ℕ) (ν : 𝓞 K) : ℝ :=
  primePowerConductorWeight v e * ‖primePowerPrimitiveCubicCoefficient v (e+1) ν‖

theorem weightedLocalCubicCoefficient_nonneg
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (e : ℕ) (ν : 𝓞 K) :
    0 ≤ weightedLocalCubicCoefficient v e ν := by
  unfold weightedLocalCubicCoefficient primePowerConductorWeight
  positivity

theorem weightedLocalCubicCoefficient_eq_completion
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (e : ℕ) (ν : 𝓞 K) :
    weightedLocalCubicCoefficient v e ν =
      weightedCubicIncrement (v.adicCompletionIntegers K)
        (algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν) e := by
  simp only [weightedLocalCubicCoefficient, primePowerConductorWeight,
    primePowerPrimitiveCubicCoefficient_succ, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, normalizedPrimePowerCubicCount_eq_completion,
    weightedCubicIncrement, cubicConductorWeight, completion_residue_card_eq_absNorm]

def cubicUniformLocalWeightedMass
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ℝ :=
  if (6 : ResidueField (v.adicCompletionIntegers K)) ≠ 0 then
    3096 / (Ideal.absNorm v.asIdeal : ℝ)^2
  else cubicBadPrimeWeightedMass (v.adicCompletionIntegers K)

theorem cubicUniformLocalWeightedMass_nonneg
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    0 ≤ cubicUniformLocalWeightedMass v := by
  unfold cubicUniformLocalWeightedMass cubicBadPrimeWeightedMass
  split_ifs <;> positivity

theorem cubicUniformLocalWeightedMass_summable :
    Summable (cubicUniformLocalWeightedMass (K := K)) := by
  have h : Summable (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      3096 / (Ideal.absNorm v.asIdeal : ℝ)^2) := by
    have hs := (primeIdeal_norm_rpow_summable (K := K) (by norm_num : (1 : ℝ) < 2)).mul_left 3096
    convert hs using 1
    funext v
    rw [Real.rpow_neg (Nat.cast_nonneg _)]
    norm_num [Real.rpow_natCast, div_eq_mul_inv]
  apply h.congr_cofinite
  filter_upwards [good_cubic_residue_primes_cofinite (K := K)] with v hv
  simp only [cubicUniformLocalWeightedMass, if_pos hv]

/-- The majorant is chosen before the target, including at primes above 2 or 3. -/
theorem weightedLocalCubicCoefficient_summable_bound
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (ν : 𝓞 K) :
    Summable (fun e => weightedLocalCubicCoefficient v e ν) ∧
      (∑' e, weightedLocalCubicCoefficient v e ν) ≤ cubicUniformLocalWeightedMass v := by
  letI := completionIntegers_henselianLocalRing v
  letI := completionIntegers_residueFinite v
  letI := completionIntegers_charZero v
  simp only [weightedLocalCubicCoefficient_eq_completion]
  unfold cubicUniformLocalWeightedMass
  split_ifs with h6
  · simpa only [completion_residue_card_eq_absNorm] using
      weightedCubicIncrement_good_summable_bound h6
        (algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν)
  · exact weightedCubicIncrement_all_primes_summable_bound (by norm_num)
      (algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν)

theorem weightedLocalCubicCoefficient_global_summable (ν : 𝓞 K) :
    Summable (fun ve : IsDedekindDomain.HeightOneSpectrum (𝓞 K) × ℕ =>
      weightedLocalCubicCoefficient ve.1 ve.2 ν) := by
  apply (summable_prod_of_nonneg (fun ve => weightedLocalCubicCoefficient_nonneg ve.1 ve.2 ν)).mpr
  refine ⟨fun v => (weightedLocalCubicCoefficient_summable_bound v ν).1, ?_⟩
  apply cubicUniformLocalWeightedMass_summable.of_nonneg_of_le
    (fun v => tsum_nonneg (fun e => weightedLocalCubicCoefficient_nonneg v e ν))
  intro v
  exact (weightedLocalCubicCoefficient_summable_bound v ν).2

theorem weightedLocalCubicCoefficient_global_tsum_le (ν : 𝓞 K) :
    (∑' ve : IsDedekindDomain.HeightOneSpectrum (𝓞 K) × ℕ,
      weightedLocalCubicCoefficient ve.1 ve.2 ν) ≤
        ∑' v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), cubicUniformLocalWeightedMass v := by
  rw [(weightedLocalCubicCoefficient_global_summable ν).tsum_prod]
  apply Summable.tsum_le_tsum (fun v => (weightedLocalCubicCoefficient_summable_bound v ν).2)
  · exact (weightedLocalCubicCoefficient_global_summable ν).prod
  · exact cubicUniformLocalWeightedMass_summable

end WaringSiegel

#print axioms WaringSiegel.weightedLocalCubicCoefficient_global_tsum_le
