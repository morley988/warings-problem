import WaringSiegel.WSL4ArchArcWeights
import WaringSiegel.WSL3IdealPoissonCubicEnlarged

/-! # Root-profile Poisson bounds with the full growing packing factor

The constant is independent of the ideal, scale, cubic frequency and enlargement.
In particular a growing Y may appear explicitly; it is not absorbed in a fixed-L
major-arc constant.
-/
noncomputable section
open MeasureTheory Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3 WaringSiegel.WSL3Poisson
open scoped BigOperators Classical NumberField nonZeroDivisors SchwartzMap
namespace WaringSiegel.WSL4
set_option maxHeartbeats 1000000
variable {K : Type*} [Field K] [NumberField K]

theorem smoothRootCubic_residue_packing_bound (rho R : ℝ) (hrho : 0<rho) (hR : 0<R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (I : Ideal (𝓞 K)) (hI : I ≠ 0),
      ∀ [Fintype (𝓞 K ⧸ I)] (F : (𝓞 K ⧸ I) → ℂ) (B : ℝ), 0 ≤ B →
      (∀ ξ : (inverseDifferent K*(I : FractionalIdeal (𝓞 K)⁰ K)⁻¹),
        ‖idealCompleteTraceFactor I F (mixedEmbedding K (ξ:K))‖ ≤ B) →
      ∀ (P : ℝ), 0 < P → ∀ θ : mixedSpace K,
      ‖∑' x : 𝓞 K, F (Ideal.Quotient.mk I x)*
        (smoothRootWeight rho R (P⁻¹ • mixedEmbedding K (x:K)) •
          archimedeanTraceCharacter θ ((mixedEmbedding K (x:K))^3))‖ ≤
        C*(B/(I.absNorm:ℝ))*P^(finrank ℚ K)/cubicProductStationaryWeight (P^3 • θ) *
          (1+(I.absNorm:ℝ)*productArcWeight (P^3) θ/P^(finrank ℚ K)) := by
  obtain ⟨C,hC,hb⟩ := smoothCubic_residue_sum_bound (K:=K) rho R hrho hR
  let E := cubicMajorRadiusConstant K R
  have hE : 0 ≤ E := cubicMajorRadiusConstant_nonneg R
  let c := basisCovolume (NumberField.mixedEmbedding.latticeBasis K)
  have hc : 0 < c := basisCovolume_pos _
  refine ⟨C*(1+E)/c,by positivity,fun I hI inst F B hB hcomplete P hP θ => ?_⟩
  let q := (I.absNorm:ℝ)*productArcWeight (P^3) θ/P^(finrank ℚ K)
  have hq : 0 ≤ q := div_nonneg (mul_nonneg (Nat.cast_nonneg _) (productArcWeight_pos _ _).le)
    (pow_nonneg hP.le _)
  have hmaj : (I.absNorm:ℝ)*productArcWeight (P^3) θ ≤ q*P^(finrank ℚ K) := by
    dsimp only [q]
    rw [div_mul_cancel₀ _ (pow_ne_zero _ hP.ne')]
  have hratio := cubicDualRadius_norm_ratio_le_enlarged q I R P hP θ hmaj
  have hpack : 1+(∏ w, (cubicDualRadius R P θ w)^(mult w))/
      (FractionalIdeal.absNorm (inverseDifferent K*(I : FractionalIdeal (𝓞 K)⁰ K)⁻¹):ℝ) ≤
      (1+E)*(1+q) := by
    have heq : 1+E*q ≤ (1+E)*(1+q) := by nlinarith
    exact (add_le_add_left hratio 1).trans heq
  apply (hb I hI F B hB hcomplete P hP θ).trans
  have hh := mul_le_mul_of_nonneg_left hpack
    (show 0 ≤ C*B*P^(finrank ℚ K)/((I.absNorm:ℝ)*c*cubicProductStationaryWeight (P^3 • θ)) from
      div_nonneg (mul_nonneg (mul_nonneg hC.le hB) (pow_nonneg hP.le _))
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hc.le) (cubicProductStationaryWeight_pos _).le))
  exact hh.trans_eq (by dsimp only [q,c]; simp only [div_eq_mul_inv,mul_inv]; ring)

theorem smoothRootCubic_center_packing_bound (rho R : ℝ) (hrho : 0<rho) (hR : 0<R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : K) (κ : ℝ), 0 ≤ κ →
      (∀ ξ : (inverseDifferent K*(traceConductor γ : FractionalIdeal (𝓞 K)⁰ K)⁻¹),
        ‖fieldCenterCompleteSum 3 γ (mixedEmbedding K (ξ:K))‖ ≤
          ((traceConductor γ).absNorm:ℝ)*κ) →
      ∀ (P : ℝ), 0 < P → ∀ θ : mixedSpace K,
      ‖∑' x : 𝓞 K, smoothRootWeight rho R (P⁻¹ • mixedEmbedding K (x:K)) •
        archimedeanTraceCharacter (mixedEmbedding K γ+θ) ((mixedEmbedding K (x:K))^3)‖ ≤
          C*κ*P^(finrank ℚ K)/cubicProductStationaryWeight (P^3 • θ) *
            (1+((traceConductor γ).absNorm:ℝ)*productArcWeight (P^3) θ/P^(finrank ℚ K)) := by
  obtain ⟨C,hC,hb⟩ := smoothRootCubic_residue_packing_bound (K:=K) rho R hrho hR
  refine ⟨C,hC,fun γ κ hκ hfinite P hP θ => ?_⟩
  letI := fieldCenterResidueFintype γ
  have hN : 0 < ((traceConductor γ).absNorm:ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero ((Ideal.absNorm_ne_zero_iff (traceConductor γ)).mpr inferInstance))
  have h := hb (traceConductor γ) (traceConductor_ne_zero γ)
    (fun q => fieldCenterResidueChar γ (q^3)) (((traceConductor γ).absNorm:ℝ)*κ)
    (mul_nonneg hN.le hκ) (by intro ξ; exact hfinite ξ) P hP θ
  have hquot : (((traceConductor γ).absNorm:ℝ)*κ)/((traceConductor γ).absNorm:ℝ) = κ := by
    field_simp
  rw [hquot] at h
  have he : (∑' x : 𝓞 K, smoothRootWeight rho R (P⁻¹ • mixedEmbedding K (x:K)) •
      archimedeanTraceCharacter (mixedEmbedding K γ+θ) ((mixedEmbedding K (x:K))^3)) =
      ∑' x : 𝓞 K, fieldCenterResidueChar γ ((Ideal.Quotient.mk (traceConductor γ) x)^3)*
        (smoothRootWeight rho R (P⁻¹ • mixedEmbedding K (x:K)) •
          archimedeanTraceCharacter θ ((mixedEmbedding K (x:K))^3)) := by
    apply tsum_congr
    intro x
    rw [← (Ideal.Quotient.mk (traceConductor γ)).map_pow x 3,
      fieldCenterResidueChar_mk,traceCharacter_frequency_add]
    simp only [map_pow,Complex.real_smul]
    ring
  rw [he]
  exact h


theorem smoothRootCubic_residue_arc_packing_bound (rho R : ℝ) (hrho : 0<rho) (hR : 0<R) :
    ∃ C : ℝ, 0<C ∧ ∀ (I : Ideal (𝓞 K)) (hI : I≠0),
      ∀ [Fintype (𝓞 K ⧸ I)] (F : (𝓞 K ⧸ I) → ℂ) (B : ℝ), 0≤B →
      (∀ ξ : (inverseDifferent K*(I : FractionalIdeal (𝓞 K)⁰ K)⁻¹),
        ‖idealCompleteTraceFactor I F (mixedEmbedding K (ξ:K))‖≤B) →
      ∀ P : ℝ, 0<P → ∀ θ : mixedSpace K,
      ‖∑' x : 𝓞 K,F (Ideal.Quotient.mk I x)*
        (smoothRootWeight rho R (P⁻¹ • mixedEmbedding K (x:K)) •
          archimedeanTraceCharacter θ ((mixedEmbedding K (x:K))^3))‖ ≤
        C*(B/(I.absNorm:ℝ))*P^finrank ℚ K*(productArcWeight (P^3) θ)^(-(1/2):ℝ)*
          (1+(I.absNorm:ℝ)*productArcWeight (P^3) θ/P^finrank ℚ K) := by
  obtain ⟨C,hC,hb⟩ := smoothRootCubic_residue_packing_bound (K:=K) rho R hrho hR
  refine ⟨C,hC,fun I hI inst F B hB hcomplete P hP θ => ?_⟩
  have hA := productArcWeight_pos (P^3) θ
  have hfreq : (productArcWeight (P^3) θ)^((1:ℝ)/2) ≤
      cubicProductStationaryWeight (P^3 • θ) :=
    (productArcWeight_rpow_le_frequencyWeight _ (pow_nonneg hP.le _) _ (by norm_num) _).trans
      (cubicProductFrequencyWeight_le_stationary le_rfl _)
  have hh := div_le_div_of_nonneg_left
    (show 0≤C*(B/(I.absNorm:ℝ))*P^finrank ℚ K by positivity)
    (Real.rpow_pos_of_pos hA ((1:ℝ)/2)) hfreq
  apply (hb I hI F B hB hcomplete P hP θ).trans
  apply (mul_le_mul_of_nonneg_right hh (by positivity)).trans_eq
  rw [Real.rpow_neg hA.le]
  rfl

#print axioms smoothRootCubic_residue_packing_bound
#print axioms smoothRootCubic_center_packing_bound
#print axioms smoothRootCubic_residue_arc_packing_bound
end WaringSiegel.WSL4
