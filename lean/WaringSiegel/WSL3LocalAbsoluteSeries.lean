import WaringSiegel.WSL3LocalVariation
import WaringSiegel.WSL2CubicEulerProduct

/-! # WSL3: absolute summability of the actual cubic conductor coefficients -/
noncomputable section
open IsLocalRing Filter Topology
open scoped BigOperators Classical NumberField
namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

theorem primePowerPrimitiveCubicCoefficient_norm_sum_range_le
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h6 : (6 : ResidueField (v.adicCompletionIntegers K)) ≠ 0)
    (ν : 𝓞 K) (N : ℕ) :
    (∑ e ∈ Finset.range N, ‖primePowerPrimitiveCubicCoefficient v (e+1) ν‖) ≤
      3096 / (Ideal.absNorm v.asIdeal : ℝ)^3 := by
  letI := completionIntegers_henselianLocalRing v
  letI := completionIntegers_residueFinite v
  simp only [primePowerPrimitiveCubicCoefficient_succ, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, normalizedPrimePowerCubicCount_eq_completion]
  simpa only [completion_residue_card_eq_absNorm] using
    normalized_cubic_total_variation_bound h6 N
      (algebraMap (𝓞 K) (v.adicCompletionIntegers K) ν)

theorem primePowerPrimitiveCubicCoefficient_norm_summable
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ν : 𝓞 K} (hν : ν ≠ 0) :
    Summable (fun e : ℕ => ‖primePowerPrimitiveCubicCoefficient v (e+1) ν‖) := by
  apply summable_of_finite_support
  simpa only [Function.support, norm_ne_zero_iff] using
    primePowerPrimitiveCubicCoefficient_finite_support v hν

theorem primePowerPrimitiveCubicCoefficient_norm_tsum_le
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h6 : (6 : ResidueField (v.adicCompletionIntegers K)) ≠ 0)
    {ν : 𝓞 K} (hν : ν ≠ 0) :
    (∑' e : ℕ, ‖primePowerPrimitiveCubicCoefficient v (e+1) ν‖) ≤
      3096 / (Ideal.absNorm v.asIdeal : ℝ)^3 := by
  apply le_of_tendsto (primePowerPrimitiveCubicCoefficient_norm_summable v hν).hasSum.tendsto_sum_nat
  exact Filter.Eventually.of_forall (primePowerPrimitiveCubicCoefficient_norm_sum_range_le v h6 ν)

theorem cubicConductorAbsoluteError_summable :
    Summable (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      3096 / (Ideal.absNorm v.asIdeal : ℝ)^3) := by
  have h := (primeIdeal_norm_rpow_summable (K := K) (by norm_num : (1 : ℝ) < 3)).mul_left 3096
  convert h using 1
  funext v
  rw [Real.rpow_neg (Nat.cast_nonneg _)]
  norm_num [Real.rpow_natCast, div_eq_mul_inv]

/-- The sum over prime ideals of the local absolute conductor masses is finite.
The exceptional primes are treated by actual stabilization, not an assumed bound. -/
theorem primePowerPrimitiveCubicCoefficient_global_norm_summable
    {ν : 𝓞 K} (hν : ν ≠ 0) :
    Summable (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      ∑' e : ℕ, ‖primePowerPrimitiveCubicCoefficient v (e+1) ν‖) := by
  apply cubicConductorAbsoluteError_summable.of_norm_bounded_eventually
  filter_upwards [good_cubic_residue_primes_cofinite (K := K)] with v hv
  rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg (fun _ => norm_nonneg _))]
  exact primePowerPrimitiveCubicCoefficient_norm_tsum_le v hv hν

theorem primePowerPrimitiveCubicCoefficient_pair_norm_summable
    {ν : 𝓞 K} (hν : ν ≠ 0) :
    Summable (fun ve : IsDedekindDomain.HeightOneSpectrum (𝓞 K) × ℕ =>
      ‖primePowerPrimitiveCubicCoefficient ve.1 (ve.2+1) ν‖) := by
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  exact ⟨fun v => primePowerPrimitiveCubicCoefficient_norm_summable v hν,
    primePowerPrimitiveCubicCoefficient_global_norm_summable hν⟩

end WaringSiegel

#print axioms WaringSiegel.primePowerPrimitiveCubicCoefficient_norm_tsum_le
#print axioms WaringSiegel.primePowerPrimitiveCubicCoefficient_pair_norm_summable
