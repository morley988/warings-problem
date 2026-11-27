import WaringSiegel.WSL3IdealPoissonPowerApproximation
import WaringSiegel.WSL3IdealPoissonCenter

/-!
# Genuine every-degree major main term at every actual field center

Only the trivial finite complete-sum bound is used. The explicit error is
arbitrarily small with the dual radius-volume ratio, uniformly in conductor,
center, scale, target frequency, and all real/complex aspect ratios.
-/
noncomputable section
open MeasureTheory Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3
open scoped BigOperators Classical NumberField nonZeroDivisors SchwartzMap
namespace WaringSiegel.WSL3Poisson
set_option maxHeartbeats 700000
variable {K : Type*} [Field K] [NumberField K]

theorem smoothPower_center_main_error (k : ℕ) (rho R : ℝ) (hrho : 0 < rho) (hR : 0 < R) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : K) (P : ℝ), 0 < P → ∀ θ : mixedSpace K,
      ‖(∑' x : 𝓞 K, smoothRootWeight rho R (P⁻¹ • mixedEmbedding K (x:K)) •
          archimedeanTraceCharacter (mixedEmbedding K γ+θ) ((mixedEmbedding K (x:K))^k)) -
        (P^(finrank ℚ K)/(((traceConductor γ).absNorm:ℝ)*
          basisCovolume (NumberField.mixedEmbedding.latticeBasis K))) •
          (fieldCenterCompleteSum k γ 0 * weightedRootIntegral k (smoothRootWeight rho R) (P^k • θ))‖ ≤
        C*P^(finrank ℚ K)*(powerDualVolumeRatio k R P θ (traceConductor γ))^N*
          (1+powerDualVolumeRatio k R P θ (traceConductor γ)) := by
  obtain ⟨C,hC,hb⟩ := smoothPower_residue_main_error (K:=K) k rho R hrho hR N
  refine ⟨C,hC,fun γ P hP θ => ?_⟩
  letI := fieldCenterResidueFintype γ
  have hN : 0 < ((traceConductor γ).absNorm:ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero ((Ideal.absNorm_ne_zero_iff (traceConductor γ)).mpr inferInstance))
  have hcard : Fintype.card (𝓞 K ⧸ traceConductor γ) = (traceConductor γ).absNorm := by
    rw [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]
  have hF : (∑ q : 𝓞 K ⧸ traceConductor γ, ‖fieldCenterResidueChar γ (q^k)‖) =
      ((traceConductor γ).absNorm:ℝ) := by
    simp only [(fieldCenterResidueChar γ).norm_apply,Finset.sum_const,Finset.card_univ,
      nsmul_eq_mul,mul_one,hcard]
  have h := hb (traceConductor γ) (traceConductor_ne_zero γ)
    (fun q => fieldCenterResidueChar γ (q^k)) P hP θ
  rw [hF,div_self hN.ne',mul_one] at h
  have he : (∑' x : 𝓞 K, smoothRootWeight rho R (P⁻¹ • mixedEmbedding K (x:K)) •
      archimedeanTraceCharacter (mixedEmbedding K γ+θ) ((mixedEmbedding K (x:K))^k)) =
      ∑' x : 𝓞 K, fieldCenterResidueChar γ ((Ideal.Quotient.mk (traceConductor γ) x)^k)*
        (smoothRootWeight rho R (P⁻¹ • mixedEmbedding K (x:K)) •
          archimedeanTraceCharacter θ ((mixedEmbedding K (x:K))^k)) := by
    apply tsum_congr
    intro x
    rw [← (Ideal.Quotient.mk (traceConductor γ)).map_pow x k,
      fieldCenterResidueChar_mk,traceCharacter_frequency_add]
    simp only [map_pow,Complex.real_smul]
    ring
  rw [he]
  exact h

#print axioms smoothPower_center_main_error
end WaringSiegel.WSL3Poisson
