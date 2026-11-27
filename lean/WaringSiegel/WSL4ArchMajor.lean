import WaringSiegel.WSL4ArchPoissonBound

/-! # Actual near-zero source on fixed enlarged conductor major arcs -/
noncomputable section
open MeasureTheory Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson
open scoped BigOperators Classical NumberField nonZeroDivisors SchwartzMap
namespace WaringSiegel.WSL4
set_option maxHeartbeats 1000000
variable {K : Type*} [Field K] [NumberField K]

theorem nearZeroCubic_residue_major_bound_enlarged (L : ℝ) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (I : Ideal (𝓞 K)) (hI : I ≠ 0),
      ∀ [Fintype (𝓞 K ⧸ I)] (F : (𝓞 K ⧸ I) → ℂ) (B : ℝ), 0 ≤ B →
      (∀ ξ : (inverseDifferent K*(I : FractionalIdeal (𝓞 K)⁰ K)⁻¹),
        ‖idealCompleteTraceFactor I F (mixedEmbedding K (ξ:K))‖ ≤ B) →
      ∀ (P : ℝ), 0 < P → ∀ θ : mixedSpace K,
      (I.absNorm:ℝ)*productArcWeight (P^3) θ ≤ L*P^(finrank ℚ K) →
      ‖∑' x : 𝓞 K, F (Ideal.Quotient.mk I x)*
        (nearZeroWeight (P⁻¹ • mixedEmbedding K (x:K)) •
          archimedeanTraceCharacter θ ((mixedEmbedding K (x:K))^3))‖ ≤
        C*(B/(I.absNorm:ℝ))*P^(finrank ℚ K)/cubicProductFrequencyWeight (1/3) (P^3 • θ) := by
  obtain ⟨C,hC,hb⟩ := nearZeroCubic_residue_sum_bound (K:=K) 
  let A := cubicMajorRadiusConstant K (1/2)*L
  have hA : 0 ≤ A := mul_nonneg (cubicMajorRadiusConstant_nonneg (1/2)) hL
  let c := basisCovolume (NumberField.mixedEmbedding.latticeBasis K)
  have hc : 0 < c := basisCovolume_pos _
  refine ⟨C*(1+A)/c,by positivity,fun I hI inst F B hB hcomplete P hP θ hmaj => ?_⟩
  apply (hb I hI F B hB hcomplete P hP θ).trans
  have hI0 : 0 ≤ (I.absNorm:ℝ) := Nat.cast_nonneg _
  have hh := mul_le_mul_of_nonneg_left (add_le_add_left
    (cubicDualRadius_norm_ratio_le_enlarged L I (1/2) P hP θ hmaj) 1)
    (show 0 ≤ C*B*P^(finrank ℚ K)/((I.absNorm:ℝ)*c*cubicProductFrequencyWeight (1/3) (P^3 • θ)) from
      div_nonneg (mul_nonneg (mul_nonneg hC.le hB) (pow_nonneg hP.le _))
        (mul_nonneg (mul_nonneg hI0 hc.le) (cubicProductFrequencyWeight_pos (1/3) _).le))
  exact hh.trans_eq (by dsimp only [A,c]; simp only [div_eq_mul_inv,mul_inv]; ring)

/-- Actual major-arc cubic estimate. The displayed finite twisted-sum hypothesis
is deliberately retained: the pure cubic Gauss bound does not imply it. -/
theorem nearZeroCubic_center_major_bound_enlarged (L : ℝ) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : K) (κ : ℝ), 0 ≤ κ →
      (∀ ξ : (inverseDifferent K*(traceConductor γ : FractionalIdeal (𝓞 K)⁰ K)⁻¹),
        ‖fieldCenterCompleteSum 3 γ (mixedEmbedding K (ξ:K))‖ ≤
          ((traceConductor γ).absNorm:ℝ)*κ) →
      ∀ (P : ℝ), 0 < P → ∀ θ : mixedSpace K,
      ((traceConductor γ).absNorm:ℝ)*productArcWeight (P^3) θ ≤ L*P^(finrank ℚ K) →
      ‖∑' x : 𝓞 K, nearZeroWeight (P⁻¹ • mixedEmbedding K (x:K)) •
        archimedeanTraceCharacter (mixedEmbedding K γ+θ) ((mixedEmbedding K (x:K))^3)‖ ≤
          C*κ*P^(finrank ℚ K)/cubicProductFrequencyWeight (1/3) (P^3 • θ) := by
  obtain ⟨C,hC,hb⟩ := nearZeroCubic_residue_major_bound_enlarged (K:=K) L hL
  refine ⟨C,hC,fun γ κ hκ hfinite P hP θ hmaj => ?_⟩
  letI := fieldCenterResidueFintype γ
  have hN : 0 < ((traceConductor γ).absNorm:ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero ((Ideal.absNorm_ne_zero_iff (traceConductor γ)).mpr inferInstance))
  have h := hb (traceConductor γ) (traceConductor_ne_zero γ)
    (fun q => fieldCenterResidueChar γ (q^3)) (((traceConductor γ).absNorm:ℝ)*κ)
    (mul_nonneg hN.le hκ) (by intro ξ; exact hfinite ξ) P hP θ hmaj
  have hquot : (((traceConductor γ).absNorm:ℝ)*κ)/((traceConductor γ).absNorm:ℝ) = κ := by
    field_simp
  rw [hquot] at h
  have he : (∑' x : 𝓞 K, nearZeroWeight (P⁻¹ • mixedEmbedding K (x:K)) •
      archimedeanTraceCharacter (mixedEmbedding K γ+θ) ((mixedEmbedding K (x:K))^3)) =
      ∑' x : 𝓞 K, fieldCenterResidueChar γ ((Ideal.Quotient.mk (traceConductor γ) x)^3)*
        (nearZeroWeight (P⁻¹ • mixedEmbedding K (x:K)) •
          archimedeanTraceCharacter θ ((mixedEmbedding K (x:K))^3)) := by
    apply tsum_congr
    intro x
    rw [← (Ideal.Quotient.mk (traceConductor γ)).map_pow x 3,
      fieldCenterResidueChar_mk,traceCharacter_frequency_add]
    simp only [map_pow,Complex.real_smul]
    ring
  rw [he]
  exact h

#print axioms nearZeroCubic_residue_major_bound_enlarged
#print axioms nearZeroCubic_center_major_bound_enlarged
end WaringSiegel.WSL4
