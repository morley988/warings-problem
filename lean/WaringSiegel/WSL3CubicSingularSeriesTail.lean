import WaringSiegel.WSL3ConductorWeightedIdeal
import WaringSiegel.WSL3CubicSingularSeriesPositive

/-! # WSL3: a target-uniform power-saving tail for the literal cubic singular series -/
noncomputable section
set_option maxHeartbeats 800000
open Filter Topology
open scoped BigOperators Classical NumberField
namespace WaringSiegel
variable {K : Type*} [Field K] [NumberField K]

theorem idealPrimitiveCubicCoefficient_norm_cuberoot_uniform_bound (ν : 𝓞 K) :
    Summable (fun I : {I : Ideal (𝓞 K) // I ≠ 0} =>
      (Ideal.absNorm I.1 : ℝ)^(1/3 : ℝ) * ‖idealPrimitiveCubicCoefficient I.1 I.2 ν‖) ∧
    (∑' I : {I : Ideal (𝓞 K) // I ≠ 0},
      (Ideal.absNorm I.1 : ℝ)^(1/3 : ℝ) * ‖idealPrimitiveCubicCoefficient I.1 I.2 ν‖) ≤
        cubicUniformSingularSeriesConstant K := by
  obtain ⟨hs,hb⟩ := idealPrimitiveCubicCoefficient_weighted_uniform_bound ν
  have hle (I : {I : Ideal (𝓞 K) // I ≠ 0}) :
      (Ideal.absNorm I.1 : ℝ)^(1/3 : ℝ) * ‖idealPrimitiveCubicCoefficient I.1 I.2 ν‖ ≤
        idealCubicConductorWeight I * ‖idealPrimitiveCubicCoefficient I.1 I.2 ν‖ :=
    mul_le_mul_of_nonneg_right (idealCubicConductorWeight_ge_norm_cuberoot I) (norm_nonneg _)
  have hsum := hs.of_nonneg_of_le (fun I => by positivity) hle
  exact ⟨hsum, (hsum.tsum_le_tsum hle hs).trans hb⟩

theorem idealPrimitiveCubicCoefficient_norm_summable_all_targets (ν : 𝓞 K) :
    Summable (fun I : {I : Ideal (𝓞 K) // I ≠ 0} =>
      ‖idealPrimitiveCubicCoefficient I.1 I.2 ν‖) := by
  apply (idealPrimitiveCubicCoefficient_norm_cuberoot_uniform_bound ν).1.of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro I
  have hI : 1 ≤ (Ideal.absNorm I.1 : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (mt Ideal.absNorm_eq_zero_iff.mp I.2)
  exact le_mul_of_one_le_left (norm_nonneg _)
    (Real.one_le_rpow hI (by norm_num))

/-- The absolute conductor tail has a power saving with one constant for all targets. -/
theorem cubicSingularSeries_absolute_tail_bound (ν : 𝓞 K) (Q : ℝ) (hQ : 0 < Q) :
    (∑' I : {I : {I : Ideal (𝓞 K) // I ≠ 0} // Q < (Ideal.absNorm I.1 : ℝ)},
      ‖idealPrimitiveCubicCoefficient I.1.1 I.1.2 ν‖) ≤
        cubicUniformSingularSeriesConstant K / Q^(1/3 : ℝ) := by
  let S : Set {I : Ideal (𝓞 K) // I ≠ 0} := {I | Q < (Ideal.absNorm I.1 : ℝ)}
  obtain ⟨hs,hb⟩ := idealPrimitiveCubicCoefficient_norm_cuberoot_uniform_bound ν
  have hn := idealPrimitiveCubicCoefficient_norm_summable_all_targets ν
  have hns := hn.subtype S
  have hss := hs.subtype S
  change Summable (fun I : S => ‖idealPrimitiveCubicCoefficient I.1.1 I.1.2 ν‖) at hns
  change Summable (fun I : S => (Ideal.absNorm I.1.1 : ℝ)^(1/3 : ℝ) *
    ‖idealPrimitiveCubicCoefficient I.1.1 I.1.2 ν‖) at hss
  have hsub : (∑' I : S, (Ideal.absNorm I.1.1 : ℝ)^(1/3 : ℝ) *
      ‖idealPrimitiveCubicCoefficient I.1.1 I.1.2 ν‖) ≤ cubicUniformSingularSeriesConstant K := by
    exact (Summable.tsum_subtype_le _ S (fun I => by positivity) hs).trans hb
  have hle (I : S) :
      Q^(1/3 : ℝ) * ‖idealPrimitiveCubicCoefficient I.1.1 I.1.2 ν‖ ≤
        (Ideal.absNorm I.1.1 : ℝ)^(1/3 : ℝ) * ‖idealPrimitiveCubicCoefficient I.1.1 I.1.2 ν‖ := by
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow hQ.le I.2.le (by norm_num)) (norm_nonneg _)
  have hsum := (hns.mul_left (Q^(1/3 : ℝ))).tsum_le_tsum hle hss
  rw [hns.tsum_mul_left] at hsum
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hQ _)).mpr
  simpa only [mul_comm] using hsum.trans hsub

def cubicConductorCutoff (Q : ℕ) : Finset {I : Ideal (𝓞 K) // I ≠ 0} :=
  ((Ideal.finite_setOf_absNorm_le Q).preimage
    (f := fun I : {I : Ideal (𝓞 K) // I ≠ 0} => I.1)
    (fun _ _ _ _ h => Subtype.ext h)).toFinset

@[simp] theorem mem_cubicConductorCutoff (Q : ℕ) (I : {I : Ideal (𝓞 K) // I ≠ 0}) :
    I ∈ cubicConductorCutoff Q ↔ Ideal.absNorm I.1 ≤ Q := by
  simp only [cubicConductorCutoff, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_setOf_eq]

def cubicSingularSeriesTruncation (Q : ℕ) (ν : 𝓞 K) : ℂ :=
  ∑ I ∈ cubicConductorCutoff Q, idealPrimitiveCubicCoefficient I.1 I.2 ν

/-- The finite sum of the literal ideal-conductor coefficients approximates
the full singular series uniformly in every algebraic-integer target. -/
theorem cubicSingularSeries_truncation_error (Q : ℕ) (hQ : 0 < Q) (ν : 𝓞 K) :
    ‖cubicSingularSeries ν - cubicSingularSeriesTruncation Q ν‖ ≤
      cubicUniformSingularSeriesConstant K / (Q : ℝ)^(1/3 : ℝ) := by
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
  exact he'.trans_le (cubicSingularSeries_absolute_tail_bound ν (Q : ℝ) (by exact_mod_cast hQ))

end WaringSiegel

#print axioms WaringSiegel.cubicSingularSeries_truncation_error
