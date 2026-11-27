import WaringSiegel.WSL3ConductorUniformMass

/-! # WSL3: a uniform weighted absolute norm for the actual ideal singular series -/
noncomputable section
set_option maxHeartbeats 800000
open Filter Topology
open scoped BigOperators Classical NumberField
namespace WaringSiegel

theorem tsum_finset_products_le_exp {ι : Type*} (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (hs : Summable f) :
    (∑' S : Finset ι, ∏ i ∈ S, f i) ≤ Real.exp (∑' i, f i) := by
  have hp := hasProd_one_add_of_hasSum_prod (summable_finset_products_of_nonneg f hf hs).hasSum
  apply le_of_tendsto hp
  apply Filter.Eventually.of_forall
  intro S
  calc
    (∏ i ∈ S, (1+f i)) ≤ ∏ i ∈ S, Real.exp (f i) := by
      apply Finset.prod_le_prod (fun i _ => by linarith [hf i])
      intro i _
      linarith [Real.add_one_le_exp (f i)]
    _ = Real.exp (∑ i ∈ S, f i) := (Real.exp_sum S f).symm
    _ ≤ Real.exp (∑' i, f i) := Real.exp_le_exp.mpr (hs.sum_le_tsum S (fun i _ => hf i))

variable {K : Type*} [Field K] [NumberField K]

def idealCubicConductorWeight (I : {I : Ideal (𝓞 K) // I ≠ 0}) : ℝ :=
  ∏ ve ∈ nonzeroIdealConductorGraph I, primePowerConductorWeight ve.1 ve.2

theorem idealCubicConductorWeight_nonneg (I : {I : Ideal (𝓞 K) // I ≠ 0}) :
    0 ≤ idealCubicConductorWeight I := by
  apply Finset.prod_nonneg
  intro ve _
  unfold primePowerConductorWeight
  positivity

theorem primePowerConductorWeight_cube
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (e : ℕ) :
    (Ideal.absNorm v.asIdeal : ℝ)^(e+1) ≤ primePowerConductorWeight v e ^ 3 := by
  have hq1 : 1 ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (mt Ideal.absNorm_eq_zero_iff.mp v.ne_bot)
  unfold primePowerConductorWeight
  rw [← pow_mul]
  apply pow_le_pow_right₀ hq1
  omega

theorem idealCubicConductorWeight_cube (I : {I : Ideal (𝓞 K) // I ≠ 0}) :
    (Ideal.absNorm I.1 : ℝ) ≤ idealCubicConductorWeight I ^ 3 := by
  have hn : (Ideal.absNorm I.1 : ℝ) =
      ∏ ve ∈ nonzeroIdealConductorGraph I, (Ideal.absNorm ve.1.asIdeal : ℝ)^(ve.2+1) := by
    have h := congrArg (fun J : Ideal (𝓞 K) => (Ideal.absNorm J : ℝ))
      (nonzeroIdealConductorGraph_product I)
    simpa only [map_prod, map_pow, Nat.cast_prod, Nat.cast_pow] using h.symm
  rw [hn, idealCubicConductorWeight, ← Finset.prod_pow]
  exact Finset.prod_le_prod (fun ve _ => by positivity)
    (fun ve _ => primePowerConductorWeight_cube ve.1 ve.2)

theorem idealCubicConductorWeight_ge_norm_cuberoot (I : {I : Ideal (𝓞 K) // I ≠ 0}) :
    (Ideal.absNorm I.1 : ℝ)^(1/3 : ℝ) ≤ idealCubicConductorWeight I := by
  rw [one_div, Real.rpow_inv_le_iff_of_pos (Nat.cast_nonneg _)
    (idealCubicConductorWeight_nonneg I) (by norm_num : (0 : ℝ) < 3)]
  have h := idealCubicConductorWeight_cube I
  rw [← Real.rpow_natCast (idealCubicConductorWeight I) 3] at h
  exact h

theorem weighted_ideal_coefficient_eq_graph_product
    (I : {I : Ideal (𝓞 K) // I ≠ 0}) (ν : 𝓞 K) :
    idealCubicConductorWeight I * ‖idealPrimitiveCubicCoefficient I.1 I.2 ν‖ =
      ∏ ve ∈ nonzeroIdealConductorGraph I, weightedLocalCubicCoefficient ve.1 ve.2 ν := by
  rw [idealPrimitiveCubicCoefficient_eq_graph_product, norm_prod]
  exact (Finset.prod_mul_distrib :
    (∏ ve ∈ nonzeroIdealConductorGraph I,
      primePowerConductorWeight ve.1 ve.2 * ‖primePowerPrimitiveCubicCoefficient ve.1 (ve.2+1) ν‖) =
    _).symm

def cubicUniformSingularSeriesConstant (K : Type*) [Field K] [NumberField K] : ℝ :=
  Real.exp (∑' v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), cubicUniformLocalWeightedMass v)

theorem cubicUniformSingularSeriesConstant_pos : 0 < cubicUniformSingularSeriesConstant K :=
  Real.exp_pos _

/-- A single field-dependent constant controls the weighted absolute series
for every target, even the zero target. -/
theorem idealPrimitiveCubicCoefficient_weighted_uniform_bound (ν : 𝓞 K) :
    Summable (fun I : {I : Ideal (𝓞 K) // I ≠ 0} =>
      idealCubicConductorWeight I * ‖idealPrimitiveCubicCoefficient I.1 I.2 ν‖) ∧
    (∑' I : {I : Ideal (𝓞 K) // I ≠ 0},
      idealCubicConductorWeight I * ‖idealPrimitiveCubicCoefficient I.1 I.2 ν‖) ≤
        cubicUniformSingularSeriesConstant K := by
  let f := fun ve : IsDedekindDomain.HeightOneSpectrum (𝓞 K) × ℕ =>
    weightedLocalCubicCoefficient ve.1 ve.2 ν
  have hf : ∀ ve, 0 ≤ f ve := fun ve => weightedLocalCubicCoefficient_nonneg ve.1 ve.2 ν
  have hs : Summable f := weightedLocalCubicCoefficient_global_summable ν
  have hfin := summable_finset_products_of_nonneg f hf hs
  have hi := hfin.comp_injective (nonzeroIdealConductorGraph_injective (K := K))
  have hsum : Summable (fun I : {I : Ideal (𝓞 K) // I ≠ 0} =>
      idealCubicConductorWeight I * ‖idealPrimitiveCubicCoefficient I.1 I.2 ν‖) := by
    apply hi.congr
    intro I
    exact (weighted_ideal_coefficient_eq_graph_product I ν).symm
  refine ⟨hsum, ?_⟩
  calc
    _ ≤ ∑' S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K) × ℕ), ∏ ve ∈ S, f ve := by
      apply Summable.tsum_le_tsum_of_inj nonzeroIdealConductorGraph
        nonzeroIdealConductorGraph_injective
        (fun S _ => Finset.prod_nonneg (fun ve _ => hf ve))
        (fun I => (weighted_ideal_coefficient_eq_graph_product I ν).le) hsum hfin
    _ ≤ Real.exp (∑' ve, f ve) := tsum_finset_products_le_exp f hf hs
    _ ≤ cubicUniformSingularSeriesConstant K :=
      Real.exp_le_exp.mpr (weightedLocalCubicCoefficient_global_tsum_le ν)

end WaringSiegel

#print axioms WaringSiegel.idealPrimitiveCubicCoefficient_weighted_uniform_bound
