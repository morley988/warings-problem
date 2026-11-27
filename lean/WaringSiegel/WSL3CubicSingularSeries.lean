import WaringSiegel.WSL3ConductorConfigurations
import WaringSiegel.WSL3ConductorFiniteProduct

/-! # WSL3: the actual cubic singular series equals its local-density Euler product -/
noncomputable section
set_option maxHeartbeats 800000
open Filter Topology
open scoped BigOperators Classical NumberField
namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

def cubicSingularSeries (ν : 𝓞 K) : ℂ :=
  ∑' I : {I : Ideal (𝓞 K) // I ≠ 0}, idealPrimitiveCubicCoefficient I.1 I.2 ν

def cubicConductorLocalFactor (ν : 𝓞 K)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ℂ :=
  1 + ∑' e : ℕ, primePowerPrimitiveCubicCoefficient v (e+1) ν

theorem cubicConductorLocalFactor_eq_density
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ν : 𝓞 K} (hν : ν ≠ 0)
    {σ : ℝ} (hσ : Tendsto (fun e => normalizedPrimePowerCubicCount v 8 e ν) atTop (𝓝 σ)) :
    cubicConductorLocalFactor ν v = (σ : ℂ) := by
  rw [cubicConductorLocalFactor, (primePowerPrimitiveCubicCoefficient_hasSum v hν hσ).tsum_eq]
  ring

theorem cubicLocalCoefficientSum_norm_summable {ν : 𝓞 K} (hν : ν ≠ 0) :
    Summable (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      ‖∑' e : ℕ, primePowerPrimitiveCubicCoefficient v (e+1) ν‖) := by
  apply (primePowerPrimitiveCubicCoefficient_global_norm_summable hν).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro v
  exact norm_tsum_le_tsum_norm (primePowerPrimitiveCubicCoefficient_norm_summable v hν)

/-- Equality of the absolutely convergent ideal character series and its
actual prime-power conductor Euler product. -/
theorem cubicSingularSeries_eq_euler_product {ν : 𝓞 K} (hν : ν ≠ 0) :
    Multipliable (cubicConductorLocalFactor ν) ∧
      cubicSingularSeries ν = ∏' v, cubicConductorLocalFactor ν v := by
  let f := fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
    ∑' e : ℕ, primePowerPrimitiveCubicCoefficient v (e+1) ν
  obtain ⟨hprod, heuler⟩ := complex_euler_finset_expansion f
    (cubicLocalCoefficientSum_norm_summable hν)
  refine ⟨hprod, ?_⟩
  have hc : Summable (fun c : ConductorConfiguration K =>
      idealPrimitiveCubicCoefficient (configurationIdeal c).1 (configurationIdeal c).2 ν) :=
    conductorConfigurationEquiv.summable_iff.mpr
      (idealPrimitiveCubicCoefficient_norm_summable hν).of_norm
  calc
    cubicSingularSeries ν = ∑' c : ConductorConfiguration K,
        idealPrimitiveCubicCoefficient (configurationIdeal c).1 (configurationIdeal c).2 ν :=
      (conductorConfigurationEquiv.tsum_eq
        (fun I => idealPrimitiveCubicCoefficient I.1 I.2 ν)).symm
    _ = ∑' S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)),
        ∑' e : S → ℕ,
          idealPrimitiveCubicCoefficient (configurationIdeal ⟨S,e⟩).1
            (configurationIdeal ⟨S,e⟩).2 ν := hc.tsum_sigma
    _ = ∑' S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)), ∏ v ∈ S, f v := by
      apply tsum_congr
      intro S
      simp only [idealPrimitiveCubicCoefficient_configuration]
      rw [(complex_finite_product_hasSum S
        (fun v e => primePowerPrimitiveCubicCoefficient v.1 (e+1) ν)
        (fun v => primePowerPrimitiveCubicCoefficient_norm_summable v.1 hν)).2.tsum_eq]
      exact Finset.prod_coe_sort S f
    _ = ∏' v, cubicConductorLocalFactor ν v := heuler.symm

end WaringSiegel

#print axioms WaringSiegel.cubicSingularSeries_eq_euler_product
