import WaringSiegel.WSL4MajorProductTails
import WaringSiegel.WSL4MajorCompactPositivity

/-! # Uniform product-truncated singular integral bounds and positivity -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory NumberField NumberField.mixedEmbedding Module
  WaringSiegel.WSL2 WaringSiegel.WSL3
open scoped NumberField Classical BigOperators
namespace WaringSiegel.WSL4
variable {K : Type*} [Field K] [NumberField K]

theorem productSingularIntegral_truncation_rpow
    (k s : ℕ) (hk : 0<k) (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R) (δ : ℝ) :
    ∃ C : ℝ, 0<C ∧ ∀ Q : ℝ, 1≤Q → ∀ b : mixedSpace K,
      ‖pairedWeightedSingularIntegral (integerLatticeSourceScale K) k (s+1)
          (smoothRootWeight ρ R) b - productSingularIntegral k (s+1) ρ R Q b‖ ≤ C/Q^δ := by
  obtain ⟨C,hC,hb⟩ := productSingularIntegral_truncation (K := K) k s hk ρ R hρ hR ⌈δ⌉₊
  refine ⟨C,hC,fun Q hQ b => ?_⟩
  have hQ0 : 0<Q := lt_of_lt_of_le zero_lt_one hQ
  apply (hb Q hQ0 b).trans
  apply div_le_div_of_nonneg_left hC.le (Real.rpow_pos_of_pos hQ0 δ)
  simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hQ (Nat.le_ceil δ)

theorem pairedSmooth_singularIntegral_uniform_norm
    (k s : ℕ) (hk : 0<k) (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R) :
    ∃ C : ℝ, 0<C ∧ ∀ b : mixedSpace K,
      ‖pairedWeightedSingularIntegral (integerLatticeSourceScale K) k (s+1)
        (smoothRootWeight ρ R) b‖≤C := by
  let F : mixedSpace K → ℝ := fun β =>
    ‖pairedWeightedRootIntegral (integerLatticeSourceScale K) k (smoothRootWeight ρ R) β^(s+1)‖
  have hn : 0≤∫ β,F β ∂archimedeanDualMeasure (integerLatticeSourceScale K) :=
    integral_nonneg (fun β => norm_nonneg _)
  refine ⟨(∫ β,F β ∂archimedeanDualMeasure (integerLatticeSourceScale K))+1,by linarith,fun b => ?_⟩
  apply (norm_integral_le_integral_norm _).trans
  simp only [norm_mul,archimedeanTraceCharacter_norm,one_mul]
  change (∫ β,F β ∂archimedeanDualMeasure (integerLatticeSourceScale K))≤_+1
  linarith

theorem productSingularIntegral_uniform_norm
    (k s : ℕ) (hk : 0<k) (ρ R : ℝ) (hρ : 0<ρ) (hR : 0<R) :
    ∃ C : ℝ, 0<C ∧ ∀ (Q : ℝ) (b : mixedSpace K),
      ‖productSingularIntegral k (s+1) ρ R Q b‖≤C := by
  let F : mixedSpace K → ℝ := fun β =>
    ‖pairedWeightedRootIntegral (integerLatticeSourceScale K) k (smoothRootWeight ρ R) β^(s+1)‖
  have hi : Integrable F (archimedeanDualMeasure (integerLatticeSourceScale K)) := by
    simpa only [pow_zero,one_mul] using pairedSmooth_product_moment_integrable (K := K)
      (integerLatticeSourceScale K) integerLatticeSourceScale_pos k s hk ρ R hρ hR 0
  have hn : 0≤∫ β,F β ∂archimedeanDualMeasure (integerLatticeSourceScale K) :=
    integral_nonneg (fun β => norm_nonneg _)
  refine ⟨(∫ β,F β ∂archimedeanDualMeasure (integerLatticeSourceScale K))+1,by linarith,fun Q b => ?_⟩
  apply (norm_integral_le_integral_norm _).trans
  simp only [norm_mul,archimedeanTraceCharacter_norm,one_mul]
  apply (setIntegral_le_integral hi (Filter.Eventually.of_forall (fun β => norm_nonneg _))).trans
  linarith

theorem exists_compact_positive_productSingularIntegral
    (k s : ℕ) (hk : 0<k) (B : ℝ) (hB : 0<B) :
    ∃ ρ R c Q0 : ℝ, 0<ρ ∧ 0<R ∧ 0<c ∧ 0<Q0 ∧
      ∀ b ∈ compactTargetSet K B,
        c≤(pairedWeightedSingularIntegral (integerLatticeSourceScale K) k (s+2)
          (smoothRootWeight ρ R) b).re ∧
        (pairedWeightedSingularIntegral (integerLatticeSourceScale K) k (s+2)
          (smoothRootWeight ρ R) b).im=0 ∧
        ∀ Q : ℝ, Q0≤Q → c≤(productSingularIntegral k (s+2) ρ R Q b).re := by
  obtain ⟨ρ,R,c,hρ,hR,hc,hpos⟩ :=
    exists_compact_lattice_smooth_singularIntegral (K := K) k (s+2) hk (by omega) B hB
  obtain ⟨C,hC,hb⟩ := productSingularIntegral_truncation (K := K) k (s+1) hk ρ R hρ hR 1
  refine ⟨ρ,R,c/2,max 1 (2*C/c),hρ,hR,by positivity,
    lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro b hbregion
  obtain ⟨hfull,hfullim⟩ := hpos b hbregion
  refine ⟨by linarith,hfullim,?_⟩
  intro Q hQ
  have hQ1 : 1≤Q := (le_max_left _ _).trans hQ
  have hQ0 : 0<Q := lt_of_lt_of_le zero_lt_one hQ1
  have hQ' : 2*C/c≤Q := (le_max_right _ _).trans hQ
  have herr := hb Q hQ0 b
  simp only [show s+1+1=s+2 by omega,pow_one] at herr
  have hsmall : C/Q≤c/2 := by
    apply (div_le_iff₀ hQ0).mpr
    have h := (div_le_iff₀ hc).mp hQ'
    nlinarith
  have hre := Complex.re_le_norm
    (pairedWeightedSingularIntegral (integerLatticeSourceScale K) k (s+2)
      (smoothRootWeight ρ R) b-productSingularIntegral k (s+2) ρ R Q b)
  rw [Complex.sub_re] at hre
  linarith

#print axioms productSingularIntegral_truncation_rpow
#print axioms productSingularIntegral_uniform_norm
#print axioms exists_compact_positive_productSingularIntegral
end WaringSiegel.WSL4
