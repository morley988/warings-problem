import WaringSiegel.WSL3IdealPoissonPowerDecay

/-!
# Quantitative actual main-term approximation for every power degree

The nonzero dual series has every power of its anisotropic radius-volume to
ideal-norm ratio. The finite complete coefficients use only their elementary
triangle bound here: no Weil, major-arc approximation, or decay hypothesis.
-/
noncomputable section
open MeasureTheory Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  WaringSiegel.WSL2 WaringSiegel.WSL3
open scoped BigOperators Classical NumberField nonZeroDivisors SchwartzMap
namespace WaringSiegel.WSL3Poisson
set_option maxHeartbeats 900000
variable {K : Type*} [Field K] [NumberField K]

def fractionalIdealZero (I : FractionalIdeal (𝓞 K)⁰ K) : I := ⟨0,I.zero_mem⟩

theorem fractionalIdeal_tsum_split_zero (I : FractionalIdeal (𝓞 K)⁰ K)
    (f : I → ℂ) (hf : Summable f) :
    (∑' ξ : I, f ξ) = f (fractionalIdealZero I)+∑' ξ : {ξ : I // (ξ:K) ≠ 0}, f ξ.val := by
  have he : (∑' ξ : {ξ : I // (ξ:K) ≠ 0}, f ξ.val) =
      ∑' ξ : I, if ξ=fractionalIdealZero I then 0 else f ξ := by
    calc
      _ = ∑' ξ : I, ({ξ : I | (ξ:K) ≠ 0} : Set I).indicator f ξ :=
        tsum_subtype {ξ : I | (ξ:K) ≠ 0} f
      _ = _ := by
        apply tsum_congr
        intro ξ
        by_cases h0 : (ξ:K) = 0
        · have hz : ξ = fractionalIdealZero I := Subtype.ext h0
          have hnot : ξ ∉ ({ξ : I | (ξ:K) ≠ 0} : Set I) := fun h => h h0
          rw [Set.indicator_of_notMem hnot,if_pos hz]
        · have hz : ξ ≠ fractionalIdealZero I := by
            intro h
            exact h0 (congrArg (fun ξ : I => (ξ:K)) h)
          have hmem : ξ ∈ ({ξ : I | (ξ:K) ≠ 0} : Set I) := h0
          rw [Set.indicator_of_mem hmem,if_neg hz]
  rw [he]
  exact hf.tsum_eq_add_tsum_ite (fractionalIdealZero I)

theorem traceFourier_scaledSmoothPower_zero (k : ℕ) (rho R : ℝ) (hrho : 0 < rho) (hR : 0 < R)
    (P : ℝ) (hP : 0 < P) (θ : mixedSpace K) :
    traceFourier (scaledSmoothPowerSchwartz k rho R hrho hR P hP.ne' θ) 0 =
      P^(finrank ℚ K) • weightedRootIntegral k (smoothRootWeight rho R) (P^k • θ) := by
  rw [traceFourier_scaledSmoothPower k rho R hrho hR P hP]
  congr 1
  simp only [smul_zero,neg_zero,smoothPowerLinearIntegral,weightedRootIntegral,
    archimedeanTraceCharacter,zero_mul,map_zero,Complex.ofReal_zero,mul_zero,Complex.exp_zero,mul_one]

def powerDualVolumeRatio (k : ℕ) (R P : ℝ) (θ : mixedSpace K) (I : Ideal (𝓞 K)) : ℝ :=
  (∏ w, (powerDualRadius k R P θ w)^mult w)/
    (FractionalIdeal.absNorm (inverseDifferent K*(I : FractionalIdeal (𝓞 K)⁰ K)⁻¹):ℝ)

/-- Every-degree actual main term plus quantitative nonzero-dual error.
The source and complete coefficient are literal; no unproved analytic premise remains. -/
theorem smoothPower_residue_main_error (k : ℕ) (rho R : ℝ) (hrho : 0 < rho) (hR : 0 < R) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (I : Ideal (𝓞 K)) (hI : I ≠ 0),
      ∀ [Fintype (𝓞 K ⧸ I)] (F : (𝓞 K ⧸ I) → ℂ) (P : ℝ), 0 < P → ∀ θ : mixedSpace K,
      ‖(∑' x : 𝓞 K, F (Ideal.Quotient.mk I x)*
          (smoothRootWeight rho R (P⁻¹ • mixedEmbedding K (x:K)) •
            archimedeanTraceCharacter θ ((mixedEmbedding K (x:K))^k))) -
        (P^(finrank ℚ K)/((I.absNorm:ℝ)*basisCovolume (NumberField.mixedEmbedding.latticeBasis K))) •
          (idealCompleteTraceFactor I F 0 * weightedRootIntegral k (smoothRootWeight rho R) (P^k • θ))‖ ≤
        C*((∑ q, ‖F q‖)/(I.absNorm:ℝ))*P^(finrank ℚ K)*
          (powerDualVolumeRatio k R P θ I)^N*(1+powerDualVolumeRatio k R P θ I) := by
  let m := finrank ℚ K*N+(finrank ℚ K+2)
  obtain ⟨C,hC,hdec⟩ := scaledSmoothPowerFourier_lattice_decay (K:=K) k rho R hrho hR m
  let c := basisCovolume (NumberField.mixedEmbedding.latticeBasis K)
  have hc : 0 < c := basisCovolume_pos _
  refine ⟨C*(2*(3:ℝ)^(finrank ℚ K))/c,by positivity,fun I hI inst F P hP θ => ?_⟩
  let D : FractionalIdeal (𝓞 K)⁰ K := inverseDifferent K*(I : FractionalIdeal (𝓞 K)⁰ K)⁻¹
  have hD : D ≠ 0 := fractionalTraceDual_ne_zero (integralIdealAsUnit I hI)
  let r := powerDualRadius k R P θ
  have hr (w : InfinitePlace K) : 0 < r w := powerDualRadius_pos k R P hP θ w
  let B : ℝ := ∑ q, ‖F q‖
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  let f := scaledSmoothPowerSchwartz k rho R hrho hR P hP.ne' θ
  let g : D → ℂ := fun ξ => idealCompleteTraceFactor I F (mixedEmbedding K (ξ:K))*
    traceFourier f (mixedEmbedding K (ξ:K))
  have hg : Summable g := by
    apply Summable.of_norm_bounded ((traceFourier_integralIdealDual_summable I hI f).norm.mul_left B)
    intro ξ
    dsimp only [g]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (idealCompleteTraceFactor_norm_le I F _) (norm_nonneg _)
  obtain ⟨hs,hcount⟩ := fractionalIdeal_nonzero_power_decay D hD r hr N
  have htail : ‖∑' ξ : {ξ : D // (ξ:K) ≠ 0}, g ξ.val‖ ≤
      (B*(C*P^(finrank ℚ K)))*
        (∑' ξ : {ξ : D // (ξ:K) ≠ 0}, latticePowerDecay m r ((ξ:D):K)) := by
    apply tsum_of_norm_bounded (hs.hasSum.mul_left (B*(C*P^(finrank ℚ K))))
    intro ξ
    dsimp only [g]
    rw [norm_mul]
    calc
      _ ≤ B*((C*P^(finrank ℚ K))*latticePowerDecay m r ((ξ:D):K)) :=
        mul_le_mul (idealCompleteTraceFactor_norm_le I F _) (hdec P hP θ ((ξ:D):K)) (norm_nonneg _) hB
      _ = _ := by ring
  have htail' := htail.trans (mul_le_mul_of_nonneg_left hcount
    (mul_nonneg hB (mul_nonneg hC.le (pow_nonneg hP.le _))))
  have hIN : 0 < (I.absNorm:ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero ((Ideal.absNorm_ne_zero_iff I).mpr inferInstance))
  have hsource : (∑' x : 𝓞 K, F (Ideal.Quotient.mk I x)*
      (smoothRootWeight rho R (P⁻¹ • mixedEmbedding K (x:K)) •
        archimedeanTraceCharacter θ ((mixedEmbedding K (x:K))^k))) =
      ∑' x : 𝓞 K, F (Ideal.Quotient.mk I x)*f (mixedEmbedding K (x:K)) := by
    apply tsum_congr
    intro x
    rw [show f (mixedEmbedding K (x:K)) =
      smoothRootWeight rho R (P⁻¹ • mixedEmbedding K (x:K)) •
        archimedeanTraceCharacter θ ((mixedEmbedding K (x:K))^k) from
          scaledSmoothPowerSchwartz_apply k rho R hrho hR P hP.ne' θ _]
  have hg0 : g (fractionalIdealZero D) = idealCompleteTraceFactor I F 0 * traceFourier f 0 := by
    simp only [g,fractionalIdealZero,map_zero]
  have hmain : (P^(finrank ℚ K)/((I.absNorm:ℝ)*c)) •
      (idealCompleteTraceFactor I F 0 * weightedRootIntegral k (smoothRootWeight rho R) (P^k • θ)) =
      ((I.absNorm:ℝ)*c)⁻¹ • g (fractionalIdealZero D) := by
    rw [hg0,traceFourier_scaledSmoothPower_zero k rho R hrho hR P hP]
    simp only [Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_inv]
    ring
  rw [hsource,poisson_ideal_residue_weight I hI F f]
  change ‖((I.absNorm:ℝ)*c)⁻¹ • (∑' ξ : D, g ξ) -
    (P^(finrank ℚ K)/((I.absNorm:ℝ)*c)) •
      (idealCompleteTraceFactor I F 0 * weightedRootIntegral k (smoothRootWeight rho R) (P^k • θ))‖ ≤ _
  rw [hmain,fractionalIdeal_tsum_split_zero D g hg,smul_add,add_sub_cancel_left,
    _root_.norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (mul_nonneg hIN.le hc.le))]
  have hh := mul_le_mul_of_nonneg_left htail'
    (show 0 ≤ ((I.absNorm:ℝ)*c)⁻¹ by positivity)
  exact hh.trans_eq (by
    dsimp only [B,r,D,c,powerDualVolumeRatio]
    simp only [div_eq_mul_inv,mul_inv]
    ring)

#print axioms fractionalIdeal_tsum_split_zero
#print axioms smoothPower_residue_main_error
end WaringSiegel.WSL3Poisson
