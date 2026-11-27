import WaringSiegel.WSL3LocalSharpWeightedSeries
import WaringSiegel.WSL3ConductorIdealSeries

/-! # WSL3: a summable target-independent majorant for local masses with conductor exponent 5/4 -/
noncomputable section
open IsLocalRing Filter Topology
open scoped BigOperators Classical NumberField
namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

def primePowerSharpConductorWeight
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (e : ℕ) : ℝ :=
  (Ideal.absNorm v.asIdeal : ℝ)^((5/4 : ℝ)*(e+1))

def sharpWeightedLocalCubicCoefficient
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (e : ℕ) (ν : 𝓞 K) : ℝ :=
  primePowerSharpConductorWeight v e * ‖primePowerPrimitiveCubicCoefficient v (e+1) ν‖

theorem sharpWeightedLocalCubicCoefficient_nonneg
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (e : ℕ) (ν : 𝓞 K) :
    0 ≤ sharpWeightedLocalCubicCoefficient v e ν := by
  unfold sharpWeightedLocalCubicCoefficient primePowerSharpConductorWeight
  positivity

theorem sharpWeightedLocalCubicCoefficient_eq_completion
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (e : ℕ) (ν : 𝓞 K) :
    sharpWeightedLocalCubicCoefficient v e ν =
      sharpWeightedCubicIncrement (v.adicCompletionIntegers K)
        (algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν) e := by
  simp only [sharpWeightedLocalCubicCoefficient, primePowerSharpConductorWeight,
    primePowerPrimitiveCubicCoefficient_succ, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, normalizedPrimePowerCubicCount_eq_completion,
    sharpWeightedCubicIncrement, sharpCubicConductorWeight, completion_residue_card_eq_absNorm]

def cubicUniformLocalSharpWeightedMass
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ℝ :=
  if (6 : ResidueField (v.adicCompletionIntegers K)) ≠ 0 then
    1548 / (Ideal.absNorm v.asIdeal : ℝ)^(5/4 : ℝ)
  else cubicBadPrimeSharpWeightedMass (v.adicCompletionIntegers K)

theorem cubicUniformLocalSharpWeightedMass_nonneg
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    0 ≤ cubicUniformLocalSharpWeightedMass v := by
  unfold cubicUniformLocalSharpWeightedMass cubicBadPrimeSharpWeightedMass
  split_ifs <;> positivity

theorem cubicUniformLocalSharpWeightedMass_summable :
    Summable (cubicUniformLocalSharpWeightedMass (K := K)) := by
  have h : Summable (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      1548 / (Ideal.absNorm v.asIdeal : ℝ)^(5/4 : ℝ)) := by
    have hs := (primeIdeal_norm_rpow_summable (K := K) (by norm_num : (1 : ℝ) < 5/4)).mul_left 1548
    convert hs using 1
    funext v
    rw [Real.rpow_neg (Nat.cast_nonneg _)]
    simp only [div_eq_mul_inv]
  apply h.congr_cofinite
  filter_upwards [good_cubic_residue_primes_cofinite (K := K)] with v hv
  simp only [cubicUniformLocalSharpWeightedMass, if_pos hv]

/-- The majorant is chosen before the target, including at primes above 2 or 3. -/
theorem sharpWeightedLocalCubicCoefficient_summable_bound
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (ν : 𝓞 K) :
    Summable (fun e => sharpWeightedLocalCubicCoefficient v e ν) ∧
      (∑' e, sharpWeightedLocalCubicCoefficient v e ν) ≤ cubicUniformLocalSharpWeightedMass v := by
  letI := completionIntegers_henselianLocalRing v
  letI := completionIntegers_residueFinite v
  letI := completionIntegers_charZero v
  simp only [sharpWeightedLocalCubicCoefficient_eq_completion]
  unfold cubicUniformLocalSharpWeightedMass
  split_ifs with h6
  · simpa only [completion_residue_card_eq_absNorm] using
      sharpWeightedCubicIncrement_good_summable_bound h6
        (algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν)
  · exact sharpWeightedCubicIncrement_all_primes_summable_bound (by norm_num)
      (algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν)

theorem sharpWeightedLocalCubicCoefficient_global_summable (ν : 𝓞 K) :
    Summable (fun ve : IsDedekindDomain.HeightOneSpectrum (𝓞 K) × ℕ =>
      sharpWeightedLocalCubicCoefficient ve.1 ve.2 ν) := by
  apply (summable_prod_of_nonneg (fun ve => sharpWeightedLocalCubicCoefficient_nonneg ve.1 ve.2 ν)).mpr
  refine ⟨fun v => (sharpWeightedLocalCubicCoefficient_summable_bound v ν).1, ?_⟩
  apply cubicUniformLocalSharpWeightedMass_summable.of_nonneg_of_le
    (fun v => tsum_nonneg (fun e => sharpWeightedLocalCubicCoefficient_nonneg v e ν))
  intro v
  exact (sharpWeightedLocalCubicCoefficient_summable_bound v ν).2

theorem sharpWeightedLocalCubicCoefficient_global_tsum_le (ν : 𝓞 K) :
    (∑' ve : IsDedekindDomain.HeightOneSpectrum (𝓞 K) × ℕ,
      sharpWeightedLocalCubicCoefficient ve.1 ve.2 ν) ≤
        ∑' v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), cubicUniformLocalSharpWeightedMass v := by
  rw [(sharpWeightedLocalCubicCoefficient_global_summable ν).tsum_prod]
  apply Summable.tsum_le_tsum (fun v => (sharpWeightedLocalCubicCoefficient_summable_bound v ν).2)
  · exact (sharpWeightedLocalCubicCoefficient_global_summable ν).prod
  · exact cubicUniformLocalSharpWeightedMass_summable

end WaringSiegel

#print axioms WaringSiegel.sharpWeightedLocalCubicCoefficient_global_tsum_le
