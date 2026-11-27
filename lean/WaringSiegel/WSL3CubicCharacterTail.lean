import WaringSiegel.WSL3CubicAbsoluteCharacters

/-! # WSL3: a uniform conductor tail before grouping cubic characters -/
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators Classical NumberField
namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

def cubicCharacterConductorNorm (c : CubicConductorCharacter K) : ℕ :=
  Ideal.absNorm c.1.1

theorem cubicCharacterContribution_weighted_uniform_bound (ν : 𝓞 K) :
    Summable (fun c : CubicConductorCharacter K =>
      (cubicCharacterConductorNorm c : ℝ)^(1/3 : ℝ) * ‖cubicCharacterContribution c ν‖) ∧
    (∑' c : CubicConductorCharacter K,
      (cubicCharacterConductorNorm c : ℝ)^(1/3 : ℝ) * ‖cubicCharacterContribution c ν‖) ≤
        cubicUniformSingularSeriesConstant K := by
  have hf (I : {I : Ideal (𝓞 K) // I ≠ 0}) :
      (∑' ψ : PrimitiveIdealCharacter I,
        (cubicCharacterConductorNorm ⟨I,ψ⟩ : ℝ)^(1/3 : ℝ) *
          ‖cubicCharacterContribution ⟨I,ψ⟩ ν‖) =
      (Ideal.absNorm I.1 : ℝ)^(1/3 : ℝ) * ‖idealPrimitiveCubicCoefficient I.1 I.2 0‖ := by
    simp only [cubicCharacterConductorNorm, tsum_mul_left,
      cubicCharacterContribution_fiber_norm_sum]
  obtain ⟨hi,hb⟩ := idealPrimitiveCubicCoefficient_norm_cuberoot_uniform_bound (0 : 𝓞 K)
  have hs : Summable (fun c : CubicConductorCharacter K =>
      (cubicCharacterConductorNorm c : ℝ)^(1/3 : ℝ) * ‖cubicCharacterContribution c ν‖) := by
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
        (cubicCharacterConductorNorm ⟨I,ψ⟩ : ℝ)^(1/3 : ℝ) *
          ‖cubicCharacterContribution ⟨I,ψ⟩ ν‖ := hs.tsum_sigma
    _ = _ := by simp only [hf]
    _ ≤ _ := hb

theorem cubicCharacterContribution_absolute_tail_bound (ν : 𝓞 K) (Q : ℝ) (hQ : 0 < Q) :
    (∑' c : {c : CubicConductorCharacter K // Q < (cubicCharacterConductorNorm c : ℝ)},
      ‖cubicCharacterContribution c.1 ν‖) ≤
        cubicUniformSingularSeriesConstant K / Q^(1/3 : ℝ) := by
  let S : Set (CubicConductorCharacter K) := {c | Q < (cubicCharacterConductorNorm c : ℝ)}
  obtain ⟨hs,hb⟩ := cubicCharacterContribution_weighted_uniform_bound ν
  have hn := cubicCharacterContribution_norm_summable ν
  have hns := hn.subtype S
  have hss := hs.subtype S
  change Summable (fun c : S => ‖cubicCharacterContribution c.1 ν‖) at hns
  change Summable (fun c : S => (cubicCharacterConductorNorm c.1 : ℝ)^(1/3 : ℝ) *
    ‖cubicCharacterContribution c.1 ν‖) at hss
  have hsub : (∑' c : S, (cubicCharacterConductorNorm c.1 : ℝ)^(1/3 : ℝ) *
      ‖cubicCharacterContribution c.1 ν‖) ≤ cubicUniformSingularSeriesConstant K := by
    exact (Summable.tsum_subtype_le _ S (fun c => by positivity) hs).trans hb
  have hle (c : S) : Q^(1/3 : ℝ) * ‖cubicCharacterContribution c.1 ν‖ ≤
      (cubicCharacterConductorNorm c.1 : ℝ)^(1/3 : ℝ) * ‖cubicCharacterContribution c.1 ν‖ := by
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hQ.le c.2.le (by norm_num)) (norm_nonneg _)
  have hsum := (hns.mul_left (Q^(1/3 : ℝ))).tsum_le_tsum hle hss
  rw [hns.tsum_mul_left] at hsum
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hQ _)).mpr
  simpa only [mul_comm] using hsum.trans hsub

end WaringSiegel
#print axioms WaringSiegel.cubicCharacterContribution_absolute_tail_bound
