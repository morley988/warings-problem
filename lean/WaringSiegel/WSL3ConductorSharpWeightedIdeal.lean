import WaringSiegel.WSL3ConductorSharpUniformMass
import WaringSiegel.WSL3ConductorWeightedIdeal

/-! # WSL3: the literal ideal singular series has a uniform 5/4 moment -/
noncomputable section
set_option maxHeartbeats 800000
open Filter Topology
open scoped BigOperators Classical NumberField
namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

def idealCubicSharpConductorWeight (I : {I : Ideal (𝓞 K) // I ≠ 0}) : ℝ :=
  ∏ ve ∈ nonzeroIdealConductorGraph I, primePowerSharpConductorWeight ve.1 ve.2

theorem idealCubicSharpConductorWeight_nonneg (I : {I : Ideal (𝓞 K) // I ≠ 0}) :
    0 ≤ idealCubicSharpConductorWeight I := by
  apply Finset.prod_nonneg
  intro ve _
  unfold primePowerSharpConductorWeight
  positivity

theorem idealCubicSharpConductorWeight_eq_norm (I : {I : Ideal (𝓞 K) // I ≠ 0}) :
    idealCubicSharpConductorWeight I = (Ideal.absNorm I.1 : ℝ)^(5/4 : ℝ) := by
  have hn : (Ideal.absNorm I.1 : ℝ) =
      ∏ ve ∈ nonzeroIdealConductorGraph I, (Ideal.absNorm ve.1.asIdeal : ℝ)^(ve.2+1) := by
    have h := congrArg (fun J : Ideal (𝓞 K) => (Ideal.absNorm J : ℝ))
      (nonzeroIdealConductorGraph_product I)
    simpa only [map_prod, map_pow, Nat.cast_prod, Nat.cast_pow] using h.symm
  rw [hn, ← Real.finset_prod_rpow]
  · apply Finset.prod_congr rfl
    intro ve _
    unfold primePowerSharpConductorWeight
    rw [mul_comm (5/4 : ℝ), show (ve.2 : ℝ)+1 = ((ve.2+1 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast_mul (Nat.cast_nonneg _)]
  · intro ve _
    positivity

theorem sharp_weighted_ideal_coefficient_eq_graph_product
    (I : {I : Ideal (𝓞 K) // I ≠ 0}) (ν : 𝓞 K) :
    idealCubicSharpConductorWeight I * ‖idealPrimitiveCubicCoefficient I.1 I.2 ν‖ =
      ∏ ve ∈ nonzeroIdealConductorGraph I, sharpWeightedLocalCubicCoefficient ve.1 ve.2 ν := by
  rw [idealPrimitiveCubicCoefficient_eq_graph_product, norm_prod]
  exact (Finset.prod_mul_distrib :
    (∏ ve ∈ nonzeroIdealConductorGraph I,
      primePowerSharpConductorWeight ve.1 ve.2 * ‖primePowerPrimitiveCubicCoefficient ve.1 (ve.2+1) ν‖) =
    _).symm

def cubicSharpUniformSingularSeriesConstant (K : Type*) [Field K] [NumberField K] : ℝ :=
  Real.exp (∑' v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), cubicUniformLocalSharpWeightedMass v)

theorem cubicSharpUniformSingularSeriesConstant_pos : 0 < cubicSharpUniformSingularSeriesConstant K :=
  Real.exp_pos _

/-- A single field-dependent constant controls the weighted absolute series
for every target, even the zero target. -/
theorem idealPrimitiveCubicCoefficient_sharp_weighted_uniform_bound (ν : 𝓞 K) :
    Summable (fun I : {I : Ideal (𝓞 K) // I ≠ 0} =>
      idealCubicSharpConductorWeight I * ‖idealPrimitiveCubicCoefficient I.1 I.2 ν‖) ∧
    (∑' I : {I : Ideal (𝓞 K) // I ≠ 0},
      idealCubicSharpConductorWeight I * ‖idealPrimitiveCubicCoefficient I.1 I.2 ν‖) ≤
        cubicSharpUniformSingularSeriesConstant K := by
  let f := fun ve : IsDedekindDomain.HeightOneSpectrum (𝓞 K) × ℕ =>
    sharpWeightedLocalCubicCoefficient ve.1 ve.2 ν
  have hf : ∀ ve, 0 ≤ f ve := fun ve => sharpWeightedLocalCubicCoefficient_nonneg ve.1 ve.2 ν
  have hs : Summable f := sharpWeightedLocalCubicCoefficient_global_summable ν
  have hfin := summable_finset_products_of_nonneg f hf hs
  have hi := hfin.comp_injective (nonzeroIdealConductorGraph_injective (K := K))
  have hsum : Summable (fun I : {I : Ideal (𝓞 K) // I ≠ 0} =>
      idealCubicSharpConductorWeight I * ‖idealPrimitiveCubicCoefficient I.1 I.2 ν‖) := by
    apply hi.congr
    intro I
    exact (sharp_weighted_ideal_coefficient_eq_graph_product I ν).symm
  refine ⟨hsum, ?_⟩
  calc
    _ ≤ ∑' S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K) × ℕ), ∏ ve ∈ S, f ve := by
      apply Summable.tsum_le_tsum_of_inj nonzeroIdealConductorGraph
        nonzeroIdealConductorGraph_injective
        (fun S _ => Finset.prod_nonneg (fun ve _ => hf ve))
        (fun I => (sharp_weighted_ideal_coefficient_eq_graph_product I ν).le) hsum hfin
    _ ≤ Real.exp (∑' ve, f ve) := tsum_finset_products_le_exp f hf hs
    _ ≤ cubicSharpUniformSingularSeriesConstant K :=
      Real.exp_le_exp.mpr (sharpWeightedLocalCubicCoefficient_global_tsum_le ν)

end WaringSiegel

#print axioms WaringSiegel.idealPrimitiveCubicCoefficient_sharp_weighted_uniform_bound
