import WaringSiegel.WSL3ConductorSharpWeightedIdeal
import WaringSiegel.WSL3CubicCharacterTail

/-! # WSL3: conductor exponent 5/4 and the uniform literal cubic series tail -/
noncomputable section
set_option maxHeartbeats 800000
open Filter Topology
open scoped BigOperators Classical NumberField
namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

theorem idealPrimitiveCubicCoefficient_norm_five_quarters_uniform_bound (ν : 𝓞 K) :
    Summable (fun I : {I : Ideal (𝓞 K) // I ≠ 0} =>
      (Ideal.absNorm I.1 : ℝ)^(5/4 : ℝ) * ‖idealPrimitiveCubicCoefficient I.1 I.2 ν‖) ∧
    (∑' I : {I : Ideal (𝓞 K) // I ≠ 0},
      (Ideal.absNorm I.1 : ℝ)^(5/4 : ℝ) * ‖idealPrimitiveCubicCoefficient I.1 I.2 ν‖) ≤
        cubicSharpUniformSingularSeriesConstant K := by
  simpa only [idealCubicSharpConductorWeight_eq_norm] using
    idealPrimitiveCubicCoefficient_sharp_weighted_uniform_bound ν

/-- The absolute conductor tail has a power saving with one constant for all targets. -/
theorem cubicSingularSeries_absolute_tail_bound_five_quarters (ν : 𝓞 K) (Q : ℝ) (hQ : 0 < Q) :
    (∑' I : {I : {I : Ideal (𝓞 K) // I ≠ 0} // Q < (Ideal.absNorm I.1 : ℝ)},
      ‖idealPrimitiveCubicCoefficient I.1.1 I.1.2 ν‖) ≤
        cubicSharpUniformSingularSeriesConstant K / Q^(5/4 : ℝ) := by
  let S : Set {I : Ideal (𝓞 K) // I ≠ 0} := {I | Q < (Ideal.absNorm I.1 : ℝ)}
  obtain ⟨hs,hb⟩ := idealPrimitiveCubicCoefficient_norm_five_quarters_uniform_bound ν
  have hn := idealPrimitiveCubicCoefficient_norm_summable_all_targets ν
  have hns := hn.subtype S
  have hss := hs.subtype S
  change Summable (fun I : S => ‖idealPrimitiveCubicCoefficient I.1.1 I.1.2 ν‖) at hns
  change Summable (fun I : S => (Ideal.absNorm I.1.1 : ℝ)^(5/4 : ℝ) *
    ‖idealPrimitiveCubicCoefficient I.1.1 I.1.2 ν‖) at hss
  have hsub : (∑' I : S, (Ideal.absNorm I.1.1 : ℝ)^(5/4 : ℝ) *
      ‖idealPrimitiveCubicCoefficient I.1.1 I.1.2 ν‖) ≤ cubicSharpUniformSingularSeriesConstant K := by
    exact (Summable.tsum_subtype_le _ S (fun I => by positivity) hs).trans hb
  have hle (I : S) :
      Q^(5/4 : ℝ) * ‖idealPrimitiveCubicCoefficient I.1.1 I.1.2 ν‖ ≤
        (Ideal.absNorm I.1.1 : ℝ)^(5/4 : ℝ) * ‖idealPrimitiveCubicCoefficient I.1.1 I.1.2 ν‖ := by
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hQ.le I.2.le (by norm_num)) (norm_nonneg _)
  have hsum := (hns.mul_left (Q^(5/4 : ℝ))).tsum_le_tsum hle hss
  rw [hns.tsum_mul_left] at hsum
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hQ _)).mpr
  simpa only [mul_comm] using hsum.trans hsub

/-- The finite sum of the literal ideal-conductor coefficients approximates
the full singular series uniformly in every algebraic-integer target. -/
theorem cubicSingularSeries_truncation_error_five_quarters (Q : ℕ) (hQ : 0 < Q) (ν : 𝓞 K) :
    ‖cubicSingularSeries ν - cubicSingularSeriesTruncation Q ν‖ ≤
      cubicSharpUniformSingularSeriesConstant K / (Q : ℝ)^(5/4 : ℝ) := by
  have hn := idealPrimitiveCubicCoefficient_norm_summable_all_targets ν
  have he := hn.of_norm.sum_add_tsum_subtype_compl (cubicConductorCutoff (K := K) Q)
  have htail : cubicSingularSeries ν - cubicSingularSeriesTruncation Q ν =
      ∑' I : {I : {I : Ideal (𝓞 K) // I ≠ 0} // I ∉ cubicConductorCutoff Q},
        idealPrimitiveCubicCoefficient I.1.1 I.1.2 ν := by
    change _ - _ = _
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using he.symm)
  rw [htail]
  have hbound := norm_tsum_le_tsum_norm (hn.subtype {I | I ∉ cubicConductorCutoff Q})
  apply hbound.trans
  let e : {I : {I : Ideal (𝓞 K) // I ≠ 0} // I ∉ cubicConductorCutoff Q} ≃
      {I : {I : Ideal (𝓞 K) // I ≠ 0} // (Q : ℝ) < (Ideal.absNorm I.1 : ℝ)} :=
    Equiv.subtypeEquivRight (fun I => by
      rw [mem_cubicConductorCutoff, not_le]
      exact Nat.cast_lt.symm)
  have he' := e.tsum_eq (fun I => ‖idealPrimitiveCubicCoefficient I.1.1 I.1.2 ν‖)
  exact he'.trans_le (cubicSingularSeries_absolute_tail_bound_five_quarters ν (Q : ℝ) (by exact_mod_cast hQ))

theorem cubicCharacterContribution_five_quarters_uniform_bound (ν : 𝓞 K) :
    Summable (fun c : CubicConductorCharacter K =>
      (cubicCharacterConductorNorm c : ℝ)^(5/4 : ℝ) * ‖cubicCharacterContribution c ν‖) ∧
    (∑' c : CubicConductorCharacter K,
      (cubicCharacterConductorNorm c : ℝ)^(5/4 : ℝ) * ‖cubicCharacterContribution c ν‖) ≤
        cubicSharpUniformSingularSeriesConstant K := by
  have hf (I : {I : Ideal (𝓞 K) // I ≠ 0}) :
      (∑' ψ : PrimitiveIdealCharacter I,
        (cubicCharacterConductorNorm ⟨I,ψ⟩ : ℝ)^(5/4 : ℝ) *
          ‖cubicCharacterContribution ⟨I,ψ⟩ ν‖) =
      (Ideal.absNorm I.1 : ℝ)^(5/4 : ℝ) * ‖idealPrimitiveCubicCoefficient I.1 I.2 0‖ := by
    simp only [cubicCharacterConductorNorm, tsum_mul_left,
      cubicCharacterContribution_fiber_norm_sum]
  obtain ⟨hi,hb⟩ := idealPrimitiveCubicCoefficient_norm_five_quarters_uniform_bound (0 : 𝓞 K)
  have hs : Summable (fun c : CubicConductorCharacter K =>
      (cubicCharacterConductorNorm c : ℝ)^(5/4 : ℝ) * ‖cubicCharacterContribution c ν‖) := by
    apply (summable_sigma_of_nonneg (fun c => by positivity)).mpr
    constructor
    · intro I
      letI := primitiveIdealCharacterFintype I
      exact Summable.of_finite
    · simpa only [hf] using hi
  refine ⟨hs, ?_⟩
  calc
    _ = ∑' I : {I : Ideal (𝓞 K) // I ≠ 0},
        ∑' ψ : PrimitiveIdealCharacter I,
        (cubicCharacterConductorNorm ⟨I,ψ⟩ : ℝ)^(5/4 : ℝ) *
          ‖cubicCharacterContribution ⟨I,ψ⟩ ν‖ := hs.tsum_sigma
    _ = _ := by simp only [hf]
    _ ≤ _ := hb

theorem cubicCharacterContribution_absolute_tail_bound_five_quarters (ν : 𝓞 K) (Q : ℝ) (hQ : 0 < Q) :
    (∑' c : {c : CubicConductorCharacter K // Q < (cubicCharacterConductorNorm c : ℝ)},
      ‖cubicCharacterContribution c.1 ν‖) ≤
        cubicSharpUniformSingularSeriesConstant K / Q^(5/4 : ℝ) := by
  let S : Set (CubicConductorCharacter K) := {c | Q < (cubicCharacterConductorNorm c : ℝ)}
  obtain ⟨hs,hb⟩ := cubicCharacterContribution_five_quarters_uniform_bound ν
  have hn := cubicCharacterContribution_norm_summable ν
  have hns := hn.subtype S
  have hss := hs.subtype S
  change Summable (fun c : S => ‖cubicCharacterContribution c.1 ν‖) at hns
  change Summable (fun c : S => (cubicCharacterConductorNorm c.1 : ℝ)^(5/4 : ℝ) *
    ‖cubicCharacterContribution c.1 ν‖) at hss
  have hsub : (∑' c : S, (cubicCharacterConductorNorm c.1 : ℝ)^(5/4 : ℝ) *
      ‖cubicCharacterContribution c.1 ν‖) ≤ cubicSharpUniformSingularSeriesConstant K := by
    exact (Summable.tsum_subtype_le _ S (fun c => by positivity) hs).trans hb
  have hle (c : S) : Q^(5/4 : ℝ) * ‖cubicCharacterContribution c.1 ν‖ ≤
      (cubicCharacterConductorNorm c.1 : ℝ)^(5/4 : ℝ) * ‖cubicCharacterContribution c.1 ν‖ := by
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hQ.le c.2.le (by norm_num)) (norm_nonneg _)
  have hsum := (hns.mul_left (Q^(5/4 : ℝ))).tsum_le_tsum hle hss
  rw [hns.tsum_mul_left] at hsum
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hQ _)).mpr
  simpa only [mul_comm] using hsum.trans hsub

end WaringSiegel
#print axioms WaringSiegel.cubicSingularSeries_truncation_error_five_quarters
#print axioms WaringSiegel.cubicCharacterContribution_absolute_tail_bound_five_quarters
